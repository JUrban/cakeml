module A = struct
  let value = 61
end

let value = 60
let local =
  let open A in
  value

let () = Printf.printf "%d:%d\n" local value
