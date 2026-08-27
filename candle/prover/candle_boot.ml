(* ------------------------------------------------------------------------- *
 * Prelude
 * ------------------------------------------------------------------------- *)

(* This is pointer equality, which is missing from CakeML.
   The way we want to implement this is by using (=) for mutable types such as
   references, and false otherwise.
   By defining (==) as follows, we get the correct behavior for reference types,
   and type errors everywhere else. Those need to be manually fixed, using (=)
   for mutable types, and false otherwise. The hope is that the type error
   messages make this decision easier.
 *)
let (==) x y = !x; !y; x = y

let ref x = Ref x;;

let (/) x y = div x y;;
let (-.) x y = Double.(-) x y;;
let (+.) x y = Double.(+) x y;;
let ( *.) x y = Double.( * ) x y;;
let (/.) x y = Double.(/) x y;;
let ( ** ) x y = Double.pow x y;;
let (||) x y = x || y;;

let log x = Double.ln x;;

(* OCaml parser doesn't like ~, and the CakeML parser doesn't like ~- nor ~-. *)
(*CML
val negint = Int.~;
val negfloat = Double.~;
*)
let (~-) x = negint x;;
let (~-.) x = negfloat x;;

let failwith msg = raise (Failure msg);;

(* This is the pretty printer for exceptions, and you need to update it
   each time you add an exception definition if you want it to print something
   informative (see e.g. exception Unchanged in lib.ml).
 *)

let pp_exn e =
  match e with
  | Chr  -> Pretty_printer.token "Chr"
  | Div  -> Pretty_printer.token "Div"
  | Bind -> Pretty_printer.token "Bind"
  | Subscript -> Pretty_printer.token "Subscript"
  | Interrupt -> Pretty_printer.token "Interrupt"
  | Failure s -> Pretty_printer.app_block "Failure" [Pretty_printer.pp_string s]
  | _ -> Pretty_printer.token "<exn>";;

(*CML
(* OCaml parser doesn't like the tilde *)
val rat_minus = Rat.~;
*)

(* Some conversions in OCaml style: *)

let string_of_int n =
  if n < 0 then "-" ^ Int.toString (-n)
  else Int.toString n
;;

let pp_int n = Pretty_printer.token (string_of_int n);;

let pp_rat r =
  let n = Rat.numerator r in
  let d = Rat.denominator r in
  Pretty_printer.token (string_of_int n ^ "/" ^ string_of_int d)
;;

let string_of_float = Double.toString;;

let int_of_string = Option.valOf o Int.fromString;;

(* Left shifting integers. HOL Light expects these to not be bigints, so I
   suppose we can just map in and out of word64. *)
let (lsl) x y =
  Word64.toInt (Word64.(<<) (Word64.fromInt x) y);;
let (lsr) x y =
  Word64.toInt (Word64.(>>) (Word64.fromInt x) y);;

let (land) x y =
  Word64.toInt (Word64.andb (Word64.fromInt x) (Word64.fromInt y));;
let (lor) x y =
  Word64.toInt (Word64.orb (Word64.fromInt x) (Word64.fromInt y));;
let (lxor) x y =
  Word64.toInt (Word64.xorb (Word64.fromInt x) (Word64.fromInt y));;
let lnot x =
  Word64.toInt (Word64.notb (Word64.fromInt x));;


(* TODO Need a better string escaping thing. *)
let string_escaped =
  let rec escape cs =
    match cs with
    | [] -> []
    | '\\'::l -> '\\'::'\\'::escape l
    | '\b'::l -> '\\'::'b'::escape l
    | '\t'::l -> '\\'::'t'::escape l
    | '\n'::l -> '\\'::'n'::escape l
    | '"'::l -> '\\'::'"'::escape l
    | c::l -> c::escape l in
  fun s -> String.implode (escape (String.explode s));;

(* Add printers for things we deal with differently, e.g. bool, app_list, etc *)

let pp_bool b = Pretty_printer.token (if b then "true" else "false");;

let pp_char c =
  Pretty_printer.token ("'" ^ string_escaped (String.str c)  ^ "'");;

let rec pp_app_list f xs =
  match xs with
  | Nil -> Pretty_printer.token "Nil"
  | List xs ->
      Pretty_printer.app_block "List" [Pretty_printer.pp_list f xs]
  | Append (l, r) ->
      Pretty_printer.app_block "Append" [
        Pretty_printer.tuple [pp_app_list f l; pp_app_list f r]]
;;

let abs x = if x < 0 then -x else x;;

let ignore x = x; ();;

let rec rev_append xs acc =
  match xs with
  | [] -> acc
  | x::xs -> rev_append xs (x::acc);;

let concat_map f =
  let rec concat acc xs =
    match acc with
    | [] -> map xs
    | a::acc -> a::concat acc xs
  and map xs =
    match xs with
    | [] -> []
    | x::xs -> concat (f x) xs in
  map;;

(* ------------------------------------------------------------------------- *
 * Helpful banner
 * ------------------------------------------------------------------------- *)

let _ = List.app print [
  "\n";
  "---------------------------------------\n";
  "                Candle                 \n";
  "---------------------------------------\n";
  "\n";
  "\n";
  ];;

(* ------------------------------------------------------------------------- *
 * Operations on filenames
 * ------------------------------------------------------------------------- *)

module Filename = struct
  let currentDir = ".";;
  let parentDir = "..";;
  let dirSep = "/";;
  let isRelative fname =
    try String.sub fname 0 <> '/'
    with Subscript -> true;;
  let concat dname fname =
    if dname = currentDir then fname
    else String.concat [dname; dirSep; fname];;
  let (basename, dirname) =
    let trimSep s = (* trim trailing separators *)
      let len = String.size s in
      let dsl = String.size dirSep in
      let rec search n =
        if n <= dsl then String.substring s 0 n
        else if String.substring s (n - dsl) dsl = dirSep then
          search (n - dsl)
        else
          String.substring s 0 n in
      search len in
    let splitPath s =
      let dsl = String.size dirSep in
      let s = trimSep s in
      let len = String.size s in
      let rec search i =
        if i < 0 then
          (currentDir, s)
        else if String.substring s i dsl = dirSep then
          let prefix = trimSep (String.substring s 0 i) in
          ((if prefix = "" then dirSep else prefix),
           String.extract s (i + dsl) None)
        else
          search (i - dsl) in
      if len = 0 then currentDir,currentDir
      else if s = dirSep then dirSep,dirSep
      else search (len - dsl) in
    ((fun s -> let _,b = splitPath s in b),
     (fun s -> let d,_ = splitPath s in d))
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Double-ended functional queue
 * ------------------------------------------------------------------------- *)

module Queue = struct
  type 'a queue = 'a list * 'a list;;
  let push_back (xs, ys) y = (xs, y::ys);;
  let push_front (xs, ys) x = (x::xs, ys);;
  let rec dequeue (xs, ys) =
    match xs with
    | x::xs -> Some (x, (xs, ys))
    | [] ->
        match ys with
        | [] -> None
        | _ -> dequeue (List.rev ys, []);;
  let empty = ([], []);;
  let flush (xs, ys) = xs @ List.rev ys;;
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Imperative wrapper around Queue
 * ------------------------------------------------------------------------- *)

module Buffer = struct
  type 'a buffer = 'a Queue.queue ref;;
  let push_back q x = q := Queue.push_back (!q) x;;
  let push_front q x = q := Queue.push_front (!q) x;;
  let dequeue q =
    match Queue.dequeue (!q) with
    | None -> None
    | Some (x, q') ->
        q := q';
        Some x;;
  let empty () = ref Queue.empty;;
  let flush q =
    let els = Queue.flush (!q) in
    q := Queue.empty;
    els
end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * Operations on strings
 * ------------------------------------------------------------------------- *)

let trimLeft str =
  let rec nom n =
    if n >= String.size str then str
    else if Char.isSpace (String.sub str n) then nom (n + 1)
    else String.extract str n None in
  nom 0
  ;;

let trimRight str =
  let rec nom n =
    if n < 1 then str
    else if Char.isSpace (String.sub str n) then nom (n - 1)
    else String.substring str 0 (n + 1) in
  nom (String.size str - 1)
;;

(* ------------------------------------------------------------------------- *
 * Operations on files
 * ------------------------------------------------------------------------- *)

let isFile fname =
  try let ins = Text_io.openIn fname in
      Text_io.closeIn ins;
      true
  with Text_io.Bad_file_name -> false
;;

(* ------------------------------------------------------------------------- *
 * Lexer for enough parts of the language to keep track on whether semi-colons
 * appear on the top-level or not.
 * ------------------------------------------------------------------------- *)

module Lexer = struct

type directive =
  | D_load
  | D_need
  | D_use
;;

let string_of_directive d =
  match d with
  | D_load -> "load"
  | D_need -> "need"
  | D_use -> "use"
;;

type token =
  | T_begin | T_end | T_struct | T_sig | T_semis | T_newline
  | T_use | T_needs | T_loads (* converted into source-loading directives *)
  | T_static_load (* exact #load selection; never reads a .cma as source *)
  | T_flyspeck_needs (* manifest-selected source load plus neutralization *)
  | T_flyspeck_loadt (* manifest-selected unconditional source load *)
  | T_other of string
  | T_symb of string
  | T_comment of string
  | T_string of string
  | T_quote of string
  | T_char of string
  | T_number of string
  | T_spaces of string
  | T_done (* pseudo-token after loading a file *)
;;

let string_of_token unquote tok =
  match tok with
  | T_begin -> "begin"
  | T_end -> "end"
  | T_struct -> "struct"
  | T_sig -> "sig"
  | T_semis -> ";;"
  | T_newline -> "\n"
  | T_string s -> "\"" ^ s ^ "\""
  | T_quote s ->
      begin
        match unquote with
        | None -> "`" ^ s ^ "`"
        | Some f -> "(" ^ f s ^ ")"
      end
  | T_char s -> "'" ^ s ^ "'"
  | T_comment s | T_other s | T_symb s | T_number s | T_spaces s -> s
  | T_use -> "#use"
  | T_loads -> "loads"
  | T_needs -> "needs"
  | T_static_load -> "#load"
  | T_flyspeck_needs -> "#flyspeck_needs"
  | T_flyspeck_loadt -> "#flyspeck_loadt"
  | T_done -> "(* shouldn't happen *)"
;;

let directive_of_token t =
  match t with
  | T_needs -> Some D_need
  | T_loads -> Some D_load
  | T_use -> Some D_use
  | _ -> None
;;

let scan nextChar peekChar =
  let quoteSym c = c = '`' in
  let tok_from_keyword =
    let keywords = [
      "begin",  T_begin;
      "end",    T_end;
      "struct", T_struct;
      "sig",    T_sig;
      (* top-level directives *)
      "#use",   T_use;
      "#load",  T_static_load;
      "#flyspeck_needs", T_flyspeck_needs;
      "#flyspeck_loadt", T_flyspeck_loadt;
      "needs",  T_needs;
      "loads",  T_loads;
    ] in
    fun s -> match Alist.lookup keywords s with
             | None -> T_other s
             | Some tok -> tok in
  let is_symbol =
    let symchars = String.explode "#$&*+-/=>@^|~!?%<:.()[]{}," in
    fun c -> List.exists (fun x -> x = c) symchars in
  let is_alpha c =
    Char.(<=) 'a' c && Char.(<=) c 'z' ||
    Char.(<=) 'A' c && Char.(<=) c 'Z' in
  let is_digit c =
    Char.(<=) '0' c && Char.(<=) c '9' in
  let is_name_char c =
    is_alpha c || is_digit c || c = '_' || c = '\'' in
  let is_int_char c =
    is_digit c || c = '_' || c = 'l' || c = 'L' || c = 'n' in
  let scan_while acc pred =
    let rec nom acc =
      Interrupt.check ();
      match peekChar () with
      | None -> None
      | Some c when pred c ->
          nextChar ();
          nom (c::acc)
      | _ -> Some (String.implode (List.rev acc)) in
    nom acc in
  let scan_comment () =
    let rec nom acc level =
      Interrupt.check ();
      if level = 0 then
        Some (String.implode ('('::'*'::List.rev acc))
      else
        match nextChar () with
        | Some '(' ->
            begin
              match peekChar () with
              | Some '*' ->
                  nextChar ();
                  nom ('*'::'('::acc) (level + 1)
              | _ -> nom ('('::acc) level
            end
        | Some '*' ->
            begin
              match peekChar () with
              | Some ')' ->
                  nextChar ();
                  nom (')'::'*'::acc) (level - 1)
              | _ -> nom ('*'::acc) level
            end
        | Some c -> nom (c::acc) level
        | None -> None in
    nom [] 1 in
  let scan_name c =
    match scan_while [c] is_name_char with
    | None -> None
    | Some s -> Some (tok_from_keyword s) in
  let scan_symb c =
    Option.map (fun s -> T_symb s)
               (scan_while [c] is_symbol) in
  let scan_int c =
    Option.map (fun s -> T_number s)
               (scan_while [c] is_int_char) in
  let scan_quote () =
    match scan_while [] (not o quoteSym) with
    | None -> None
    | Some str ->
        nextChar ();
        Some (T_quote str) in
  let skip_line () =
    scan_while [] (fun x -> x <> '\n');
    nextChar () in
  let scan_spaces c =
    Option.map (fun s -> T_spaces s)
               (scan_while [c] (fun c -> c <> '\n' && Char.isSpace c)) in
  let scan_escaped ch =
    let rec nom acc =
      Interrupt.check ();
      match nextChar () with
      | None -> None
      | Some '\\' ->
          begin
            match nextChar () with
            | None -> nom ('\\'::acc)
            | Some c -> nom (c::'\\'::acc)
          end
      | Some c when c = ch -> Some (String.implode (List.rev acc))
      | Some c -> nom (c::acc) in
    nom [] in
  let scan_strlit () =
    Option.map (fun s -> T_string s)
               (scan_escaped '"') in
  (* This code will intentionally let through some bad tokens (it doesn't check
     whether escape sequences are well formed), but those will get stuck in the
     real lexer. *)
  let scan_charlit_or_tyvar () =
    match peekChar () with
    (* Escaped character literal *)
    | Some '\\' ->
        begin
          nextChar ();
          Option.map (fun s -> T_char ("\\" ^ s))
                     (scan_escaped '\'')
        end
    (* A single tick, start of a type variable, but followed by space *)
    | Some ' ' | Some '\n' | Some '\t' | Some '\r' -> Some (T_other "'")
    (* Regular character literal, or a type variable *)
    | Some c ->
        begin
          nextChar ();
          match peekChar () with
          (* Regular character literal *)
          | Some '\'' ->
              begin
                nextChar ();
                Some (T_char (String.str c))
              end
          (* Type variable *)
          | Some _ -> Option.map (fun s -> T_other s)
                                 (scan_while [c; '\''] is_name_char)
          | None -> Some (T_other (String.implode ['\''; c]))
        end
    (* Two ticks following each other: '' *)
    | Some '\'' -> Some (T_symb "''")
    | None -> Some (T_symb "'") in
  let rec nextToken () =
    match nextChar () with
    | None -> None
    (* Attempt to scan semis *)
    | Some ';' ->
        begin
          match peekChar () with
          | Some ';' ->
              nextChar ();
              Some T_semis
          | _ -> scan_symb ';'
        end
    (* Attempt to scan comment *)
    | Some '(' ->
        begin
          match peekChar () with
          | Some '*' ->
              nextChar ();
              begin
                match scan_comment () with
                | None -> Some (T_symb "(*")
                | Some str -> Some (T_comment str)
              end
          | _ -> Some (T_symb "(")
        end
    (* Attempt to scan char literal or type variable *)
    | Some '\'' -> scan_charlit_or_tyvar ()
    (* Attempt to scan string literal *)
    | Some '"' -> scan_strlit ()
    (* A #use directive, maybe: *)
    | Some '#' -> scan_name '#'
    (* Newlines *)
    | Some '\n' -> Some T_newline
    (* Anything else *)
    | Some c ->
        if quoteSym c then
          scan_quote ()
        else if is_digit c then
          scan_int c
        else if is_symbol c then
          scan_symb c
        else if is_alpha c || c = '_' then
          scan_name c
        else if Char.isSpace c then
          scan_spaces c
        else
          Some (T_other (String.str c)) in
  fun () -> Interrupt.check (); nextToken ()
;;

end;; (* struct *)

(* ------------------------------------------------------------------------- *
 * CakeML struct: setting up REPL, reading/loading.
 * ------------------------------------------------------------------------- *)

module Cakeml = struct

let loadPath = ref [Filename.currentDir];;
(* Logical HOL Light identities for manifest-driven Flyspeck source actions.
   Keep these separate from any normalization output path: source-visible
   bookkeeping is defined by the manifest-selected original file. *)
let loadedSourceIds = ref ([]: (string * string) list);;
let pendingLoadedSourceId = ref (None: (string * string) option);;
let stdIn = Text_io.openStdIn ();;
let (input1 : (unit -> char option) ref) =
  ref (fun () -> Text_io.input1 stdIn);;

let prompt1 = ref "# ";;
let prompt2 = ref "  ";;
let userInput = ref true;;

let unquote = ref (fun (s: string) -> s);;

(* The manifest loader authenticates the sources and installs their standard
   HOL Light basename/digest identities exactly once.  Boot code deliberately
   does not hash files: [Digest.file] is part of the later HOL environment. *)
let sourceIdentities =
  ref (None: ((string * (string * string)) list) option);;

let configureSourceIdentities mappings =
  match !sourceIdentities with
  | Some _ -> failwith "Candle source identities already configured"
  | None ->
      let rec check seen remaining =
        match remaining with
        | [] -> ()
        | (original,(basename,digest))::rest ->
            if List.exists (fun path -> path = original) seen then
              failwith "duplicate Candle source identity"
            else if not (isFile original) then
              failwith ("missing Candle identity source: " ^ original)
            else if basename = "" || String.size digest <> 32 then
              failwith "malformed Candle source identity"
            else check (original::seen) rest in
      check [] mappings;
      sourceIdentities := Some mappings
;;

let sourceIdentity original =
  match !sourceIdentities with
  | None -> failwith "Candle source identities are not configured"
  | Some mappings ->
      match Alist.lookup mappings original with
      | None -> failwith ("unauthenticated Candle source action: " ^ original)
      | Some fileid -> fileid
;;

(* Source overlays are inactive during boot and can be installed exactly once
   after an outer manifest has authenticated both sides.  Resolution first
   selects an existing original source on [loadPath], then substitutes only an
   exact registered path.  An overlay directory is never added to [loadPath],
   so an unregistered file cannot shadow a pinned source. *)
let normalizationOverlay = ref (None: ((string * string) list) option);;

let configureNormalizationOverlay mappings =
  match !normalizationOverlay with
  | Some _ -> failwith "Candle normalization overlay already configured"
  | None ->
      let rec check seen remaining =
        match remaining with
        | [] -> ()
        | (original,normalized)::rest ->
            if List.exists (fun path -> path = original) seen then
              failwith "duplicate Candle normalization source"
            else if not (isFile original) then
              failwith ("missing Candle normalization source: " ^ original)
            else if not (isFile normalized) then
              failwith ("missing Candle normalized output: " ^ normalized)
            else check (original::seen) rest in
      check [] mappings;
      normalizationOverlay := Some mappings
;;

let selectNormalizedSource original =
  match !normalizationOverlay with
  | None -> original
  | Some mappings ->
      match Alist.lookup mappings original with
      | None -> original
      | Some normalized ->
          print ("- Selecting normalized source " ^ original ^ " -> " ^
                 normalized ^ "\n");
          normalized
;;

exception Repl_error;;

(* Candle links these OCaml-library compatibility modules statically.  This
   fixed-name selector is deliberately distinct from the source-file loader:
   a [.cma] is never opened or evaluated as source, and every other library
   name fails closed.  Individual Str/Unix members retain their own explicit
   compatibility checks and failures. *)
let static_library_module fname =
  match fname with
  | "unix.cma" -> Some "Unix"
  | "str.cma" -> Some "Str"
  | _ -> None
;;

let reject_static_load message =
  print ("- Static #load rejected: " ^ message ^ "\n");
  raise Repl_error
;;

let select_static_library fname =
  match static_library_module fname with
  | Some module_name ->
      print ("- Selecting statically linked library " ^ fname ^
             " (module " ^ module_name ^ ")\n")
  | None -> reject_static_load ("unsupported library " ^ fname)
;;

let reject_flyspeck_needs message =
  print ("- Static #flyspeck_needs rejected: " ^ message ^ "\n");
  raise Repl_error
;;

let reject_flyspeck_loadt message =
  print ("- Static #flyspeck_loadt rejected: " ^ message ^ "\n");
  raise Repl_error
;;

let () =
  let prompt = ref (!prompt2) in
  let pushLoad, popLoad, clearLoadStack =
    let stack = ref ([]: (string * bool) list) in
    let pushLoad fname flyspeck_action =
      stack := (fname,flyspeck_action) :: !stack in
    let popLoad () =
      match !stack with
      | fname :: rest as res -> stack := rest; Some (fname, rest)
      | _ -> None in
    let clearLoadStack () = stack := [] in
    pushLoad, popLoad, clearLoadStack in
  let peekChar, nextChar =
    let lookahead = ref (None: char option) in
    let peek () =
      match !lookahead with
      | Some c -> Some c
      | None ->
          match (!input1) () with
          | None -> None
          | Some c ->
              lookahead := Some c;
              Some c in
    let next () =
      match !lookahead with
      | None -> (!input1) ()
      | Some c ->
          lookahead := None;
          Some c in
    peek, next in
  (* Load files from disk and keep track on what has been loaded.
   *)
  let loadWithStatus =
    let loadedFiles = (ref [] : string list ref) in
    let loadMsg s = print ("- Loading " ^ s ^ "\n") in
    let load_use fname =
      loadMsg fname;
      Text_io.inputLinesFile '\n' fname in
    let load fname =
      loadMsg fname;
      match Text_io.inputLinesFile '\n' fname with
      | None -> None
      | Some lns ->
          begin
            if not (List.exists (fun x -> x = fname) (!loadedFiles)) then
              loadedFiles := fname :: !loadedFiles
          end;
          Some lns in
    let load1 fname =
      if List.exists (fun x -> x = fname) (!loadedFiles) then
        begin
          print ("- Already loaded: " ^ fname ^ "\n");
          None
        end
      else
        load fname in
    let loadOnPath pragma fname =
      let paths = List.map (fun p -> Filename.concat p fname) (!loadPath) in
      match List.find isFile paths with
      | None ->
          print ("- No such file: " ^ fname ^ "\n");
          Repl.nextString := "";
          failwith ("No such file : " ^ fname)
      | Some original ->
          let selected = selectNormalizedSource original in
          let loader = match pragma with
                       | Lexer.D_load -> load
                       | Lexer.D_need -> load1
                       | Lexer.D_use -> load_use in
          (match loader selected with
          | None -> false,[],original
          | Some ls -> true,ls,original) in
    loadOnPath in
  let load pragma fname =
    let _,lines,_ = loadWithStatus pragma fname in lines in
  (* Instantiate lexer *)
  let scan1 = Lexer.scan nextChar peekChar in
  (* Enqueue input here *)
  let input_buffer = (Buffer.empty () : Lexer.token Buffer.buffer) in
  (* Set up a nextChar/peekChar pair on the list of lines, lex all of it,
   * and then stuff it all into input_buffer.
   *)
  let scan_lines lines =
    let inp = ref lines in
    let idx = ref 0 in
    let rec peekChar () =
      match !inp with
      | [] -> None
      | s::ss ->
          try Some (String.sub s (!idx))
          with Subscript ->
            (* Look into next string. It should not be empty. *)
            match ss with
            | [] -> None
            | s::ss -> try Some (String.sub s 0)
                       with Subscript -> None in
    let rec nextChar () =
      match !inp with
      | [] -> None
      | s::ss ->
          try let res = String.sub s (!idx) in
              idx := (!idx) + 1;
              Some res
          with Subscript ->
            idx := 0;
            inp := ss;
            nextChar () in
    let scan = Lexer.scan nextChar peekChar in
    let rec nom acc =
      match scan () with
      | None -> List.app (Buffer.push_front input_buffer) (Lexer.T_done :: acc)
      | Some tok -> nom (tok::acc) in
    nom [] in
  let next () =
    match Buffer.dequeue input_buffer with
    | Some tok -> Some tok
    | None -> scan1 () in
  let output_buffer = (Buffer.empty () : Lexer.token Buffer.buffer) in
  let rec next_nonspace () =
    match next () with
    | Some (Lexer.T_spaces _) -> next_nonspace ()
    | res -> res in
  let rec append_lines left right =
    match left with
    | [] -> right
    | line::rest -> line :: append_lines rest right in
  let rec discard_phrase () =
    match next () with
    | None | Some Lexer.T_semis | Some Lexer.T_done -> ()
    | Some _ -> discard_phrase () in
  let rec scan level phrase_start =
    try match next () with
        | None -> None
        (* Static-library selection is accepted only as a complete standalone
           top-level phrase.  In particular, seeing [#load] at the start of a
           line is not sufficient if expression tokens precede it in the
           current phrase. *)
        | Some Lexer.T_static_load when level = 0 && phrase_start ->
            begin
              match next_nonspace () with
              | Some (Lexer.T_string fname) ->
                  begin
                    match next_nonspace () with
                    | Some Lexer.T_semis ->
                        select_static_library fname;
                        scan level true
                    | None ->
                        reject_static_load
                          "#load \"string\" must end with double semicolon [;;]"
                    | Some _ ->
                        discard_phrase ();
                        reject_static_load
                          "#load \"string\" must end with double semicolon [;;]"
                  end
              | None | Some Lexer.T_semis ->
                  reject_static_load
                    "#load requires one string literal and double semicolon [;;]"
              | Some _ ->
                  discard_phrase ();
                  reject_static_load
                    "#load requires one string literal and double semicolon [;;]"
            end
        | Some Lexer.T_static_load ->
            discard_phrase ();
            reject_static_load "#load must be a standalone top-level phrase"
        (* The manifest-generated full-build driver uses a distinct action.
           A new source is evaluated exactly once and followed by exactly one
           neutralization phrase.  Its completion marker is reached only after
           the evaluator has accepted both.  An already-loaded source performs
           neither step.  Any evaluator or neutralization error is observed by
           [checkError] before the marker and aborts the one-shot REPL action. *)
        | Some Lexer.T_flyspeck_needs when level = 0 && phrase_start ->
            begin
              match next_nonspace () with
              | Some (Lexer.T_string fname) ->
                  begin
                    match next_nonspace () with
                    | Some Lexer.T_semis ->
                        let selected,lines,original =
                          loadWithStatus Lexer.D_need fname in
                        if not selected then scan level true else
                          begin
                            pendingLoadedSourceId := Some (sourceIdentity original);
                            pushLoad fname true;
                            userInput := false;
                            scan_lines
                              (append_lines lines
                                ["\n(match !Cakeml.pendingLoadedSourceId with\n";
                                 " | None -> failwith \"missing Flyspeck source identity\"\n";
                                 " | Some fileid ->\n";
                                 "     if not (List.exists (fun x -> x = fileid)\n";
                                 "                          !Cakeml.loadedSourceIds) then\n";
                                 "       Cakeml.loadedSourceIds := fileid :: !Cakeml.loadedSourceIds;\n";
                                 "     Cakeml.pendingLoadedSourceId := None);;\n";
                                 "State_manager.neutralize_state ();;\n"]);
                            scan level true
                          end
                    | None ->
                        reject_flyspeck_needs
                          "#flyspeck_needs \"string\" must end with double semicolon [;;]"
                    | Some _ ->
                        discard_phrase ();
                        reject_flyspeck_needs
                          "#flyspeck_needs \"string\" must end with double semicolon [;;]"
                  end
              | None | Some Lexer.T_semis ->
                  reject_flyspeck_needs
                    "#flyspeck_needs requires one string literal and double semicolon [;;]"
              | Some _ ->
                  discard_phrase ();
                  reject_flyspeck_needs
                    "#flyspeck_needs requires one string literal and double semicolon [;;]"
            end
        | Some Lexer.T_flyspeck_needs ->
            discard_phrase ();
            reject_flyspeck_needs
              "#flyspeck_needs must be a standalone top-level phrase"
        (* Strictbuild has three manifest-selected [loadt] phrases that must
           evaluate even if their logical identity was loaded before, must add
           that identity again after success, and must not neutralize state.
           Keep this distinct from [#flyspeck_needs], whose duplicate and
           neutralization observations differ. *)
        | Some Lexer.T_flyspeck_loadt when level = 0 && phrase_start ->
            begin
              match next_nonspace () with
              | Some (Lexer.T_string fname) ->
                  begin
                    match next_nonspace () with
                    | Some Lexer.T_semis ->
                        let selected,lines,original =
                          loadWithStatus Lexer.D_load fname in
                        if not selected then
                          failwith "Candle Flyspeck loadt source read failed"
                        else
                          begin
                            pendingLoadedSourceId := Some (sourceIdentity original);
                            pushLoad fname true;
                            userInput := false;
                            scan_lines
                              (append_lines lines
                                ["\n(match !Cakeml.pendingLoadedSourceId with\n";
                                 " | None -> failwith \"missing Flyspeck loadt source identity\"\n";
                                 " | Some fileid ->\n";
                                 "     Cakeml.loadedSourceIds := fileid :: !Cakeml.loadedSourceIds;\n";
                                 "     Cakeml.pendingLoadedSourceId := None);;\n"]);
                            scan level true
                          end
                    | None ->
                        reject_flyspeck_loadt
                          "#flyspeck_loadt \"string\" must end with double semicolon [;;]"
                    | Some _ ->
                        discard_phrase ();
                        reject_flyspeck_loadt
                          "#flyspeck_loadt \"string\" must end with double semicolon [;;]"
                  end
              | None | Some Lexer.T_semis ->
                  reject_flyspeck_loadt
                    "#flyspeck_loadt requires one string literal and double semicolon [;;]"
              | Some _ ->
                  discard_phrase ();
                  reject_flyspeck_loadt
                    "#flyspeck_loadt requires one string literal and double semicolon [;;]"
            end
        | Some Lexer.T_flyspeck_loadt ->
            discard_phrase ();
            reject_flyspeck_loadt
              "#flyspeck_loadt must be a standalone top-level phrase"
        (* Treat an ordinary loading token as a directive only at the exact
           start of a complete top-level phrase.  Elsewhere [needs] and [loads]
           remain ordinary identifiers for the real parser; in particular a
           definition, conditional, or function body cannot be executed
           lexically as a load action. *)
        | Some (Lexer.T_use | Lexer.T_needs | Lexer.T_loads as tok)
          when level = 0 && phrase_start ->
            begin
              let dir = Option.valOf (Lexer.directive_of_token tok) in
              match next_nonspace () with
              (* Attempt to convert into directive: *)
              | Some (Lexer.T_string fname as tok') ->
                  begin
                    match next_nonspace () with
                    (* OK directive, perform load: *)
                    | Some (Lexer.T_semis) ->
                        let lines = load dir fname in
                        if List.null lines then scan level true else
                          begin
                            pushLoad fname false;
                            userInput := false;
                            scan_lines lines;
                            scan level true
                          end
                    (* Malformed *)
                    | _ ->
                        failwith
                          (String.concat [
                             "\nREPL error: ";
                             Lexer.string_of_directive dir;
                             " \"string\" should be followed by a double";
                             " semicolon [;;].\n"])
                  end
              (* Malformed *)
              | _ ->
                  failwith
                    (String.concat [
                       "\nREPL error: ";
                       Lexer.string_of_directive dir;
                       " should be followed by a \"string literal\" and then a";
                       " double semicolon [;;].\n"])
            end
        | Some (Lexer.T_done) ->
            (match popLoad () with
             | Some ((fname,flyspeck_action), rest) -> (
               if flyspeck_action then
                 print ("- Flyspeck source action complete: " ^ fname ^ "\n")
               else print ("- Finished loading " ^ fname ^ "\n");
               if List.null rest then userInput := true)
            | None -> failwith "candle_boot.ml: scan - should be unreachable");
            scan level phrase_start
        | Some tok ->
            Buffer.push_back output_buffer tok;
            match tok with
            | Lexer.T_begin | Lexer.T_struct | Lexer.T_sig ->
                scan (level + 1) false
            | Lexer.T_end -> scan (level - 1) false
            | Lexer.T_semis when level = 0 ->
                prompt := !prompt1;
                Some (Buffer.flush output_buffer)
            | Lexer.T_newline when !userInput ->
                print (!prompt);
                prompt := !prompt2;
                scan level phrase_start
            | Lexer.T_spaces _ | Lexer.T_comment _ | Lexer.T_newline ->
                scan level phrase_start
            | _ -> scan level false
    with Interrupt ->
      print "Compilation interrupted\n";
      raise Repl_error in
  let checkError () =
    let err = !Repl.errorMessage in
    Repl.errorMessage := "";
    if err <> "" then raise Repl_error in
  let next () =
    try checkError ();
        match scan 0 true with
        | None ->
            Repl.isEOF := true;
            Repl.nextString := ""
        | Some ts ->
            Repl.isEOF := false;
            Repl.nextString :=
              String.concat
                (List.map (Lexer.string_of_token (Some (!unquote))) ts)
    with Repl_error ->
      if not (!userInput) then print (!prompt1);
      Buffer.flush input_buffer;
      Buffer.flush output_buffer;
      clearLoadStack ();
      pendingLoadedSourceId := None;
      Repl.nextString := "";
      userInput := true in
  Repl.readNextString := (fun () ->
    print (!prompt1);
    next ();
    Repl.readNextString := next)
;;

end;; (* struct *)
