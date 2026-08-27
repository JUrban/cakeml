module Outer = struct
  let value = 1
end

open Outer.Missing

let () = ()
