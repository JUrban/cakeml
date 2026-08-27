module A = struct
  let value = 31
end

module B = struct
  let value = 32
end

open A
open A
let () = Printf.printf "%d\n" value

open B
let () = Printf.printf "%d\n" value

open A
let () = Printf.printf "%d\n" value
