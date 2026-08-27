(* open Ignored.Comment *)
let ignored_string = "open Ignored.String"
let ignored_hol_term = `open Ignored.Quotation`

module Alias = Original.Nested
module Parameterized (Input : Signature) = struct end
module Generated = functor (Input : Signature) -> Input

open Alias.Inner
open! Warned
let local = let open Local.Inner in value
include Included.Path

let packed = (module Alias : Signature)

let ignored_camlp5_pattern = `'('; let text = "(*"
