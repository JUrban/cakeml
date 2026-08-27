module A = struct
  exception Failure of int
end

module B = struct
  exception Failure of string
end

open A
let first () =
  try raise (Failure 11) with
  | Failure n -> n

open B
let second () =
  try raise (Failure "twelve") with
  | Failure s -> s

let qualified () =
  try raise (A.Failure 13) with
  | A.Failure n -> n

let () = Printf.printf "%d:%s:%d\n" (first ()) (second ()) (qualified ())
