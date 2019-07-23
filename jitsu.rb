arr = []

filename = "in.marshal"
checkIdentity = true

File.open(filename, "r") do |f|
  while true
    current_pos = f.pos
    begin
      arr += [Marshal.load(f)]
    rescue => e
      match = e.message.match(/undefined class\/module (.+)/)
      if match != nil
        name = match[1]
        puts("Create " + name)
        match = name.match(/(.+)::(.*)/)
        if match == nil
          eval("class " + name + "\nend")
        else
          if match[2] == ""
            eval("class " + match[1] + "\nend")
          else
            eval("class " + name + "\nend")
          end
        end
        f.pos = current_pos
        next
      end

      match = e.message.match(/class (.+?) needs to have method `_load'/)
      if match != nil
        name = match[1]
        puts("Create " + name + " with _load")
        eval("class " + name + "\ndef initialize data\n@metadata=data\nend\ndef self._load data\nnew(data)\nend\ndef _dump level\n@metadata\nend\nend")
        f.pos = current_pos
        next
      end

      match = e.message.match(/instance of (.+?) needs to have method `marshal_load'/)
      if match != nil
        name = match[1]
        puts("Create " + name + " with marshal_load")
        eval("class " + name + "\ndef marshal_load data\n@metadata=data\nend\ndef marshal_dump\n@metadata\nend\nend")
        f.pos = current_pos
        next
      end
      
      match = e.message.match(/end of file reached/)
      if match != nil
        puts("*** Finished ***")
        break
      end

      puts("Unhandled err : " + e.message)
      exit
    end
  end
end

require 'digest/sha2'

if checkIdentity
  data1 = ""
  arr.each{|x|
    data1 += Marshal.dump(x)
  }

  data2 = ""
  File.open(filename, "r") do |f|
    data2 = f.read
  end

  if (Digest::SHA256.hexdigest data1) != (Digest::SHA256.hexdigest data2)
    raise "Identity check failed"
  else
    puts "Identity check passed"
  end
end

# ... some processing ...

puts "Writing to " + filename + ".reconstructed"

File.open(filename + ".reconstructed", "w") do |f|
  arr.each{|x|
    Marshal.dump(x, f)
  }
end

#print(arr)
