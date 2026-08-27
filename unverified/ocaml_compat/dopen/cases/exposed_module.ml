module Package = struct
  module Inner = struct
    let value = 41
  end
end

module Inner = struct
  let value = 40
end

open Package
let () = Printf.printf "%d:%d\n" Inner.value Package.Inner.value
