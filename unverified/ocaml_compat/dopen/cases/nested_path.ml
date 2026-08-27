module Outer = struct
  module Inner = struct
    let value = 21
  end
end

open Outer.Inner
let () = Printf.printf "%d:%d\n" value Outer.Inner.value
