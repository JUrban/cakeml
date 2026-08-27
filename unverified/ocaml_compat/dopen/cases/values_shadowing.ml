module A = struct
  let value = 1
end

module B = struct
  let value = 2
end

let value = 0

open A
let () = Printf.printf "%d\n" value

open B
let () = Printf.printf "%d\n" value
let () = Printf.printf "%d\n" A.value

let value = 3
let () = Printf.printf "%d\n" value
