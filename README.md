# Ruby Marshal parser written in Rust

This program parses Marshal format, an object serialization format in Ruby language.

## Supported object types

- `;<index>` pointer to some Symbol which is already appeared on the document / `index` means how many Symbols read before this Symbol
- `:<length><string>` Symbol object (e.g. `:hello`)
- `i<int>` short (~ 32-bit) int
- `l+<length><bytes>` positive long (more than 32-bit) int
- `l-<length><bytes>` negative long (more than 32-bit) int
- `"<length><bytes>` simple ascii string
- `I"<length><bytes><length><object pairs>` string with encoding metadata
- `[<length><objects>` list
- `{<length><object pairs>` hashmap
- `T` true
- `F` false
- `o<length><name bytes><length><object pairs>` class instance
- `u<length><name bytes><length><bytes>` an instance of a class with `_load` method
- `U<length><name bytes>[<length><object pairs>` an instance of a class with `marshal_load` method
- `@<index>` pointer to some object which is already appeared on the document / `index` means how many objects read before this object
- `0` nil
- `c` class itself

## Reference

```rust
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
```

- `parse_object` :: `&[u8] -> IResult<&[u8], Object>`
  Parse given databytes as an Object.

- `parse_marshal` :: `&[u8] -> IResult<&[u8], Marshal>`
  Parse given databytes as an Marshal.

- `flatten_keypointer` :: `(obj : Object, key_table : &mut Vec<Vec<u8>>) -> Object`
  Replace all `KeyPointer` in given Object to `KeyValue`.
  Usage: `flatten_keypointer(parse_marshal(b" ....  .. . ... "), &mut vec![])`
