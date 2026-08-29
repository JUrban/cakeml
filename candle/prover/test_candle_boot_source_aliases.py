#!/usr/bin/env python3
"""Low-cost exact regression for authenticated source alias canonicalization."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
BOOT = HERE / "candle_boot.ml"


class CandleBootSourceAliasTests(unittest.TestCase):
    def test_exact_alias_resolver_compiles_and_uses_canonical_identity(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        start = source.index(
            "let sourceIdentities =\n"
            "  ref (None: ((string * (string * string)) list) option);;"
        )
        end = source.index(
            "type sourceTraceBinding =", start,
        )
        exact_resolver_source = source[start:end]
        fixture = "\n".join((
            "let isFile _ = true;;",
            "module String = struct include String let size = length end;;",
            "module Alist = struct",
            "  let rec lookup xs key =",
            "    match xs with",
            "    | [] -> None",
            "    | (candidate,value)::rest ->",
            "        if candidate = key then Some value else lookup rest key",
            "end;;",
            exact_resolver_source,
            'let canonical = "/tree/jHOLLight/a.ml";;',
            'let alias = "/tree/text_formalization/../jHOLLight/a.ml";;',
            'let identity = ("a.ml","11111111111111111111111111111111");;',
            "configureSourceIdentities [(canonical,identity)];;",
            "configureSourceAliases [(alias,canonical)];;",
            "if canonicalSourcePath alias <> canonical then",
            '  failwith "source alias did not canonicalize";;',
            "if sourceIdentity (canonicalSourcePath alias) <> identity then",
            '  failwith "source alias changed logical identity";;',
            "if canonicalSourcePath canonical <> canonical then",
            '  failwith "canonical source path changed";;',
            'print_endline "CANDLE_SOURCE_ALIAS_OK";;',
            "",
        ))
        compiler = Path("/usr/bin/ocamlc")
        self.assertTrue(compiler.is_file(), "missing OCaml compiler")
        version = subprocess.run(
            [str(compiler), "-version"], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()
        self.assertEqual(version, "4.14.1")
        with tempfile.TemporaryDirectory() as temporary:
            fixture_path = Path(temporary) / "source_aliases.ml"
            executable = Path(temporary) / "source_aliases"
            fixture_path.write_text(fixture, encoding="utf-8")
            subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=True, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            result = subprocess.run(
                [str(executable)], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stderr, "")
        self.assertEqual(result.stdout, "CANDLE_SOURCE_ALIAS_OK\n")

    def test_action_126_strictbuild_double_separator_alias_is_exact(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        concat_start = source.index("  let concat dname fname =\n")
        concat_end = source.index(";;", concat_start) + len(";;")
        concat_source = source[concat_start:concat_end].strip()
        resolver_start = source.index(
            "let sourceIdentities =\n"
            "  ref (None: ((string * (string * string)) list) option);;"
        )
        resolver_end = source.index("type sourceTraceBinding =", resolver_start)
        resolver_source = source[resolver_start:resolver_end]

        self.assertEqual(
            concat_source,
            "let concat dname fname =\n"
            "    if dname = currentDir then fname\n"
            "    else String.concat [dname; dirSep; fname];;",
        )
        self.assertIn(
            "let paths = List.map (fun p -> Filename.concat p fname) "
            "(!loadPath) in",
            source,
        )

        fixture = "\n".join((
            "let isFile _ = true;;",
            "module String = struct",
            "  include String",
            "  let size = length",
            '  let concat strings = Stdlib.String.concat "" strings',
            "end;;",
            "module Alist = struct",
            "  let rec lookup xs key =",
            "    match xs with",
            "    | [] -> None",
            "    | (candidate,value)::rest ->",
            "        if candidate = key then Some value else lookup rest key",
            "end;;",
            'let currentDir = ".";;',
            'let dirSep = "/";;',
            concat_source,
            resolver_source,
            'let flyspeck_dir = "/tree/flyspeck/text_formalization";;',
            'let loadPath = ref ["/tree/flyspeck/jHOLLight"; flyspeck_dir];;',
            "let add_to_load_path path =",
            "  if List.mem path !loadPath then ()",
            "  else loadPath := path :: !loadPath;;",
            "let _ = List.map add_to_load_path",
            "  [flyspeck_dir;",
            '   concat flyspeck_dir "../formal_ineqs";',
            '   concat flyspeck_dir "../jHOLLight/"',
            "  ];;",
            "let strictbuild_first_root = List.hd !loadPath;;",
            'let action_126_target = "../jHOLLight/caml/ssreflect.hl";;',
            "let action_126_request =",
            "  concat strictbuild_first_root action_126_target;;",
            "let exact_request =",
            '  "/tree/flyspeck/text_formalization/../jHOLLight/" ^',
            '  "/../jHOLLight/caml/ssreflect.hl";;',
            "let single_separator_forgery =",
            '  "/tree/flyspeck/text_formalization/../jHOLLight/" ^',
            '  "../jHOLLight/caml/ssreflect.hl";;',
            "let canonical =",
            '  "/tree/flyspeck/jHOLLight/caml/ssreflect.hl";;',
            'let identity = ("ssreflect.hl",',
            '  "11111111111111111111111111111111");;',
            "if strictbuild_first_root <> ",
            '   "/tree/flyspeck/text_formalization/../jHOLLight/" then',
            '  failwith "strictbuild first root lost trailing separator";;',
            "if action_126_request <> exact_request then",
            '  failwith "action 126 request lost exact double separator";;',
            "configureSourceIdentities [(canonical,identity)];;",
            "let binding =",
            '  if Sys.argv.(1) = "exact" then exact_request',
            "  else single_separator_forgery;;",
            "configureSourceAliases [(binding,canonical)];;",
            'if Sys.argv.(1) = "exact" then begin',
            "  if canonicalSourcePath action_126_request <> canonical then",
            '    failwith "exact action 126 alias did not resolve";',
            "  if sourceIdentity (canonicalSourcePath action_126_request) <>",
            "     identity then",
            '    failwith "exact action 126 alias lost identity";',
            '  print_endline "CANDLE_ACTION_126_EXACT_ALIAS_OK"',
            "end else begin",
            "  if canonicalSourcePath action_126_request <> action_126_request then",
            '    failwith "single-separator forgery matched exact request";',
            "  let rejected =",
            "    try",
            "      let _ = sourceIdentity",
            "        (canonicalSourcePath action_126_request) in false",
            "    with Failure message ->",
            '      message = "unauthenticated Candle source action: " ^',
            "                action_126_request in",
            "  if not rejected then",
            '    failwith "single-separator forged binding was accepted";',
            '  print_endline "CANDLE_ACTION_126_FORGED_ALIAS_REJECTED"',
            "end;;",
            "",
        ))
        compiler = Path("/usr/bin/ocamlc")
        self.assertTrue(compiler.is_file(), "missing OCaml compiler")
        with tempfile.TemporaryDirectory() as temporary:
            fixture_path = Path(temporary) / "action_126_alias.ml"
            executable = Path(temporary) / "action_126_alias"
            fixture_path.write_text(fixture, encoding="utf-8")
            subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=True, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            exact = subprocess.run(
                [str(executable), "exact"], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            forged = subprocess.run(
                [str(executable), "forged"], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(exact.stderr, "")
        self.assertEqual(
            exact.stdout, "CANDLE_ACTION_126_EXACT_ALIAS_OK\n",
        )
        self.assertEqual(forged.stderr, "")
        self.assertEqual(
            forged.stdout, "CANDLE_ACTION_126_FORGED_ALIAS_REJECTED\n",
        )

    def test_loader_cache_and_overlay_use_canonical_source_path(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        self.assertIn(
            "let canonical = canonicalSourcePath original in\n"
            "          let selected = selectNormalizedSource canonical in",
            source,
        )
        self.assertIn("let status = loader canonical selected in", source)
        self.assertIn(
            "List.exists (fun x -> x = original) (!loadedFiles)", source,
        )
        self.assertNotIn("match loader selected with", source)


if __name__ == "__main__":
    unittest.main()
