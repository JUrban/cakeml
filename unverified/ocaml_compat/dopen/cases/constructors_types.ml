module A = struct
  type item = Item of int
end

module B = struct
  type item = Item of string
end

open A
let a : item = Item 7

open B
let b : item = Item "eight"

let () =
  match a, b with
  | A.Item n, B.Item s -> Printf.printf "%d:%s\n" n s
