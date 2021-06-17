
use nom::{IResult, error::ParseError, named, named_args, alt, map, take, do_parse, tag};

use num_bigint::{BigInt, Sign};

use byteorder::{ByteOrder, LittleEndian};

#[derive(Debug)]
#[derive(PartialEq)]
pub struct Marshal {
    pub version_major: u8,
    pub version_minor: u8,
    pub obj: Object
}

#[derive(Debug)]
#[derive(PartialEq)]
pub enum Object {
    Int(i64),
    LongInt(BigInt),
    List(Vec<Object>),
    Hash(Vec<(Object, Object)>),
    Str(Vec<u8>), // ASCII-8BIT encoding
    StrI { content : Vec<u8>, metadata : Vec<(Object, Object)> }, // Other encoding (ASCII, UTF-8, CP932, ...)
    Instance { name : Key, map : Vec<(Object, Object)> },
    InstanceFromString { name : Key, data : Vec<u8>},
    InstanceFromArray { name : Key, data : Vec<Object>},
    True,
    False,
    Pointer(u64),
    Float(Vec<u8>),
    Nil,
    Symbol(Key),
    Class(Vec<u8>)
}

#[derive(Debug)]
#[derive(PartialEq)]
pub enum Key {
    KeyValue(Vec<u8>),
    KeyPointer(u64)
}

named_args!(parse_nbytes_int_le(length : u8)<u64>, 
  do_parse!(
    s : take!(length) >>
    (LittleEndian::read_uint(s, length as usize))
  )
);

named!(parse_byte<u8>, map!(take!(1), |c| c[0]));

/// Parse variable int.
/// 
/// # Example:
/// - 0x01ff = 255  (1byte ff)
/// - 0x02ffff = 65535  (2byte le ffff)
/// - 0x04ffffffff = 4294967295  (4byte le ffffffff)
/// - 0x05 = 0 (5 - 5)
/// - 0x06 = 1 (6 - 5)
/// - 0x07 = 2 (7 - 5)
/// - 0xff01 = -255 (0x01 - 0x100)
/// - 0xfe0201 = -65278 (0x0102 - 0x10000)
/// - 0xfd030201 = -16711165 (0x010203 - 0x1000000)
/// - 0xfc04030201 = -4278058236 (0x01020304 - 0x100000000)
/// - 0xfb = 0 (5 + 0xfb - 0x100)
/// - 0xfa = -1 (5 + 0xfb - 0x100)
/// - 0xf9 = -2 (5 + 0xfb - 0x100)
///
/// -2^32 <= return value < 2^32
///
fn parse_varint(input: &[u8]) -> IResult<&[u8], i64> {
    let (input, first_byte) = parse_byte(input)?;
    match first_byte {
        0 => Ok((input, 0)),
        1..=4 => parse_nbytes_int_le(input, first_byte)
                   .map(|(s, i)| (s, i as i64)),
        5..=0x7f => Ok((input, (first_byte - 5) as i64)),
        0x80..=0xfb => Ok((input, (first_byte as i64) - 0xfb)),
        0xfc..=0xff =>
          {
            let complement = 0xff - first_byte + 1;
            parse_nbytes_int_le(input, complement)
              .map(|(s, i)| (s, (i as i64) - (1 << 8*complement)))
          }
    }
}

///
/// Slightly modified version of many_m_n(k, k)
/// Do nothing when k=0
fn many_n<I, O, E, F>(n: i64, f: F) -> impl Fn(I) -> IResult<I, Vec<O>, E>
where
  I: Clone + PartialEq,
  F: Fn(I) -> IResult<I, O, E>,
  E: ParseError<I>,
{
  move |i: I| {
    let mut res = Vec::with_capacity(n as usize);
    let mut input = i.clone();
    let mut count: usize = 0;

    if n == 0 {
      return Ok((input, res));
    }

    loop {
      let _i = input.clone();
      match f(_i) {
        Ok((i, o)) => {
          // do not allow parsers that do not consume input (causes infinite loops)
          if i == input {
            return Err(nom::Err::Error(E::from_error_kind(input, nom::error::ErrorKind::ManyMN)));
          }

          res.push(o);
          input = i;
          count += 1;

          if count == n as usize {
            return Ok((input, res));
          }
        }
        Err(nom::Err::Error(e)) => {
          if count < n as usize {
            return Err(nom::Err::Error(E::append(input, nom::error::ErrorKind::ManyMN, e)));
          } else {
            return Ok((input, res));
          }
        }
        Err(e) => {
          return Err(e);
        }
      }
    }
  }
}

macro_rules! many_n(
  ($i:expr, $n: expr, $submac:ident!( $($args:tt)* )) => (
    many_n!($i, $n, |i| $submac!(i, $($args)*))
  );
  ($i:expr, $n: expr, $f:expr) => (
    many_n($n, $f)($i)
  );
);

named!(parse_key<Key>, alt!(
  do_parse!(
      tag!(b":") >>
      vi : parse_varint >>
      key : take!(vi) >>
      (Key::KeyValue(key.to_vec()))
  ) |
  do_parse!(
      tag!(b";") >>
      pointer : parse_varint >>
      (Key::KeyPointer(pointer as u64))
  )
));

named!(parse_pair<(Object, Object)>,do_parse!(
  key : parse_object >>
  value : parse_object >>
  ((key, value))
));

named!(parse_int<Object>, do_parse!(
    tag!(b"i") >>
    vi : parse_varint >>
    (Object::Int(vi as i64))
));

named!(parse_long_positive<Object>, do_parse!(
    tag!(b"l+") >>
    vi : parse_varint >>
    s : take!(vi*2) >> 
    (Object::LongInt(BigInt::from_bytes_le(Sign::Plus, s)))
));

named!(parse_long_negative<Object>, do_parse!(
    tag!(b"l-") >>
    vi : parse_varint >>
    s : take!(vi*2) >> 
    (Object::LongInt(BigInt::from_bytes_le(Sign::Minus, s)))
));

named!(parse_string<Object>, do_parse!(
    tag!(b"\"") >>
    vi1 : parse_varint >>
    content : take!(vi1) >>
    (Object::Str(content.to_vec()))
));

named!(parse_string_i<Object>, do_parse!(
    tag!(b"I\"") >>
    vi1 : parse_varint >>
    content : take!(vi1) >>
    vi2 : parse_varint >>
    metadata : many_n!(vi2, parse_pair) >>
    (Object::StrI {content : content.to_vec(), metadata : metadata})
));

named!(parse_list<Object>, do_parse!(
    tag!(b"[") >>
    vi : parse_varint >>
    res : many_n!(vi, parse_object) >>
    (Object::List(res))
));

named!(parse_hash<Object>, do_parse!(
    tag!(b"{") >>
    vi : parse_varint >>
    relations : many_n!(vi, parse_pair) >>
    (Object::Hash(relations))
));

named!(parse_true<Object>, do_parse!(
    tag!(b"T") >> (Object::True)
));

named!(parse_false<Object>, do_parse!(
    tag!(b"F") >> (Object::False)
));

named!(parse_instance<Object>, do_parse!(
    tag!(b"o") >>
    key : parse_key >>
    vi : parse_varint >>
    relations : many_n!(vi, parse_pair) >>
    (Object::Instance{name : key, map : relations})
));

named!(parse_instance_from_string<Object>, do_parse!(
    tag!(b"u") >>
    key : parse_key >>
    vi : parse_varint >>
    data : take!(vi) >>
    (Object::InstanceFromString{name : key, data : data.to_vec()})
));

named!(parse_instance_from_array<Object>, do_parse!(
    tag!(b"U") >>
    key : parse_key >>
    tag!(b"[") >>
    vi : parse_varint >>
    res : many_n!(vi, parse_object) >>
    (Object::InstanceFromArray{name : key, data : res})
));

named!(parse_pointer<Object>, do_parse!(
    tag!(b"@") >>
    vi : parse_varint >>
    (Object::Pointer(vi as u64))
));

named!(parse_float<Object>, do_parse!(
    tag!(b"f") >>
    vi : parse_varint >>
    content : take!(vi) >>
    (Object::Float(content.to_vec()))
));

named!(parse_nil<Object>, do_parse!(
    tag!(b"0") >>
    (Object::Nil)
));

named!(parse_symbol<Object>, do_parse!(
    key : parse_key >>
    (Object::Symbol(key))
));

named!(parse_class<Object>, do_parse!(
    tag!(b"c") >>
    vi : parse_varint >>
    name : take!(vi) >>
    (Object::Class(name.to_vec()))
));

named!(pub parse_object<Object>, alt!(
  parse_int |
  parse_long_positive |
  parse_long_negative |
  parse_string |
  parse_string_i |
  parse_list |
  parse_hash |
  parse_true |
  parse_false |
  parse_instance |
  parse_instance_from_string |
  parse_instance_from_array |
  parse_pointer |
  parse_float |
  parse_nil |
  parse_symbol |
  parse_class
));

named!(pub parse_marshal<Marshal>, do_parse!(
    maj : parse_byte >>
    min : parse_byte >>
    obj : parse_object >>
    (Marshal { version_major : maj, version_minor : min, obj : obj })
));

/// 
/// Replace all `KeyPointer` in given Object to `KeyValue`.
/// 
/// Usage: ```rust
///   assert_eq!(
///     flatten_keypointer(parse_marshal(b"\x04\x08\x5b\x09\x3a\x08\x61\x61\x61\x3b\x00\x3b\x00\x3b\x00").unwrap().1.obj, &mut vec![]),
///     Object::List(vec![
///       Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
///       Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
///       Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
///       Object::Symbol(Key::KeyValue(b"aaa".to_vec()))
///     ])
///   );
/// ```
pub fn flatten_keypointer(obj : Object, key_table : &mut Vec<Vec<u8>>) -> Object {
  let single_map = |x : Vec<Object>, kt : &mut Vec<Vec<u8>>|{
    x.into_iter().map(|a| flatten_keypointer(a, kt)).collect()
  };

  let pair_map = |x : Vec<(Object, Object)>, kt : &mut Vec<Vec<u8>>|{
    x.into_iter().map(|(a, b)| (flatten_keypointer(a, kt), flatten_keypointer(b, kt))).collect()
  };

  let k_proc = |x : Key, kt : &mut Vec<Vec<u8>>|{match x {
    Key::KeyPointer(i) => {
      let v = &kt[i as usize];
      Key::KeyValue(v.to_vec())
    },
    Key::KeyValue(v) => {
      kt.push(v.to_vec());
      Key::KeyValue(v.to_vec())
    }
  }};

  let kt = key_table;

  match obj {
    Object::List(vo) => 
    Object::List(single_map(vo, kt)),
    Object::Hash(vt) => 
    Object::Hash(pair_map(vt, kt)),
    Object::StrI { content : vu, metadata : vt } => 
    Object::StrI { content : vu, metadata : pair_map(vt, kt) },
    Object::Instance { name : k, map : vt } => 
    Object::Instance { name : k_proc(k, kt), map : pair_map(vt, kt) },
    Object::InstanceFromString { name : k, data : vu } => 
    Object::InstanceFromString { name : k_proc(k, kt), data : vu},
    Object::InstanceFromArray { name : k, data : vo } => 
    Object::InstanceFromArray { name : k_proc(k, kt), data : single_map(vo, kt) },
    Object::Symbol(k) => Object::Symbol(k_proc(k, kt)),
    _  => obj
  }
}

// fn main() -> std::io::Result<()>  {
//   let mut file = File::open("in.marshal")?;
//   let mut contents = vec![];
//   file.read_to_end(&mut contents)?;
//   match parse_marshal(&contents) {
//     Ok((remain, result1)) => {
//       match parse_marshal(&remain) {
//         Ok((_, result2)) => {
//           println!("{:?}", flatten_keypointer(result1.obj, &mut vec![]));
//           println!("{:?}", flatten_keypointer(result2.obj, &mut vec![]));
//           Ok(())
//         },
//         Err(_) => Ok(())
//       }
//     },
//     Err(_) => Ok(())
//   }
// }

// useful script:
// encoding
//   puts(Marshal.dump(".....").unpack("H*")[0].gsub(/(..)/, '\\x\1'))

#[cfg(test)]
mod tests {
  use std::num::ParseIntError;

  use super::*;

  #[test]
  fn test_list() {
    let emp : &[u8] = b"";

    assert_eq!(
      parse_list(b"[\x00"),
      Ok((emp, Object::List(vec![])))
    );

    assert_eq!(
      parse_list(b"[\x06F"),
      Ok((emp, Object::List(vec![Object::False])))
    );
  }

  #[test]
  fn test_symbol() {
    assert_eq!(
      flatten_keypointer(parse_marshal(b"\x04\x08\x5b\x09\x3a\x08\x61\x61\x61\x3b\x00\x3b\x00\x3b\x00").unwrap().1.obj, &mut vec![]),
      Object::List(vec![
        Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
        Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
        Object::Symbol(Key::KeyValue(b"aaa".to_vec())),
        Object::Symbol(Key::KeyValue(b"aaa".to_vec()))
      ])
    );
  }

  #[test]
  fn test_hash() {
    
  }

  #[test]
  fn test_string() {
    let emp : &[u8] = b"";

    // Marshal.dump("テストだよ")
    assert_eq!(
      parse_marshal(b"\x04\x08\x49\x22\x14\xe3\x83\x86\xe3\x82\xb9\xe3\x83\x88\xe3\x81\xa0\xe3\x82\x88\x06\x3a\x06\x45\x54"),
      Ok((emp, Marshal {
        version_major: 4,
        version_minor: 8,
        obj: Object::StrI {
          content : "テストだよ".as_bytes().to_vec(),
          metadata : vec![
            (
              Object::Symbol(Key::KeyValue("E".as_bytes().to_vec())),
              Object::True
            )
          ]
        }
      }))
    );

    // Marshal.dump("テストだよ".force_encoding("cp932"))
    assert_eq!(
      parse_marshal(b"\x04\x08\x49\x22\x14\xe3\x83\x86\xe3\x82\xb9\xe3\x83\x88\xe3\x81\xa0\xe3\x82\x88\x06\x3a\x0d\x65\x6e\x63\x6f\x64\x69\x6e\x67\x22\x10\x57\x69\x6e\x64\x6f\x77\x73\x2d\x33\x31\x4a"),
      Ok((emp, Marshal {
        version_major: 4,
        version_minor: 8,
        obj: Object::StrI {
          content : "テストだよ".as_bytes().to_vec(),
          metadata : vec![
            (
              Object::Symbol(Key::KeyValue("encoding".as_bytes().to_vec())),
              Object::Str("Windows-31J".as_bytes().to_vec())
            )
          ]
        }
      })));

      // Marshal.dump(["abc", "def", "ghi"])

      assert_eq!(
      parse_marshal(b"\x04\x08\x5b\x08\x49\x22\x08\x61\x62\x63\x06\x3a\x06\x45\x54\x49\x22\x08\x64\x65\x66\x06\x3b\x00\x54\x49\x22\x08\x67\x68\x69\x06\x3b\x00\x54"),
      Ok((emp, Marshal {
        version_major: 4,
        version_minor: 8,
        obj: Object::List(vec![
          Object::StrI {
            content : "abc".as_bytes().to_vec(),
            metadata : vec![
              (
                Object::Symbol(Key::KeyValue("E".as_bytes().to_vec())),
                Object::True
              )
            ]
          },
          Object::StrI {
            content : "def".as_bytes().to_vec(),
            metadata : vec![
              (
                Object::Symbol(Key::KeyPointer(0)),
                Object::True
              )
            ]
          },
          Object::StrI {
            content : "ghi".as_bytes().to_vec(),
            metadata : vec![
              (
                Object::Symbol(Key::KeyPointer(0)),
                Object::True
              )
            ]
          }
        ])
      })));
  }

  #[test]
  fn test_instance() {
    
  }

  #[test]
  fn test_parse_integer() {
    let emp : &[u8] = b"";
    assert_eq!(parse_marshal(b"\x04\x08\x69\x02\xFF\xFF"), Ok((emp, Marshal {
      version_major: 4,
      version_minor: 8,
      obj: Object::Int(65535)
    })));
    assert_eq!(parse_marshal(b"\x04\x08\x5B\x06\x69\xFD\xB9\x0B\xEF"), Ok((emp, Marshal {
      version_major: 4,
      version_minor: 8,
      obj: Object::List(vec![Object::Int(-1111111)])
    })));
    assert_eq!(parse_marshal(b"\x04\x08\x69\xF5"), Ok((emp, Marshal {
      version_major: 4,
      version_minor: 8,
      obj: Object::Int(-6)
    })));
  }

  #[test]
  fn test_varint() {
      fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
          (0..s.len())
              .step_by(2)
              .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
              .collect()
      }

      fn varint_check(bytes: &str, value: i64) {
          assert_eq!(parse_varint(&decode_hex(bytes).unwrap()).unwrap().1, value);
      }

      varint_check("01ff", 255);
      varint_check("02ffff", 65535);
      varint_check("04ffffffff", 4294967295);
      varint_check("05", 0);
      varint_check("06", 1);
      varint_check("07", 2);
      varint_check("ff01", -255);
      varint_check("fe0201", -65278);
      varint_check("fd030201", -16711165);
      varint_check("fc04030201", -4278058236);
      varint_check("fb", 0);
      varint_check("fa", -1);
      varint_check("f9", -2);
  }
}
