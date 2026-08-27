#!/usr/bin/env python3
"""Unit tests for the fail-closed bootstrap directive scanner."""

from __future__ import annotations

import unittest

from scan_bootstrap_directives import Directive, check_contract, scan


class BootstrapDirectiveTests(unittest.TestCase):
    def test_exact_allowlist(self) -> None:
        source = '''
(* #load "not-code.cma";; *)
let decoy = "#load \\"not-code.cma\\";;";;
`#load "not-code.cma";;`
#load "unix.cma";;
#load "str.cma";;
'''
        directives = scan(source)
        self.assertEqual(
            directives,
            [Directive(5, "load", "unix.cma"), Directive(6, "load", "str.cma")],
        )
        check_contract(directives)

    def test_unknown_library_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "contract mismatch"):
            check_contract(scan('#load "unix.cma";;\n#load "dynlink.cma";;\n'))

    def test_unknown_directive_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "unsupported bootstrap directives"):
            check_contract(scan('#load "unix.cma";;\n#use "str.cma";;\n'))

    def test_malformed_directive_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "malformed or unsupported directive"):
            scan('#load "unix.cma"\n')

    def test_directive_after_code_fails_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "directive-like # after code"):
            scan('let x = 0;; #load "unix.cma";;\n#load "str.cma";;\n')

    def test_primed_identifiers_do_not_hide_directives(self) -> None:
        source = '''
#load "unix.cma";;
#load "str.cma";;
let x' = '#';;
#load "dynlink.cma";;
let y' = 1;;
'''
        with self.assertRaisesRegex(ValueError, "contract mismatch"):
            check_contract(scan(source))


if __name__ == "__main__":
    unittest.main()
