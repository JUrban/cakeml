module Original = struct
  let value = 51
end

module Alias = Original
open Alias

let () = Printf.printf "%d:%d\n" value Original.value
