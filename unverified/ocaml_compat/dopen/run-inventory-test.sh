#!/bin/sh

set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/cakeml-dopen-inventory.XXXXXX")
trap 'rm -rf -- "$tmp_dir"' EXIT HUP INT TERM

cd "$script_dir"
./open_inventory.py inventory_fixture.ml > "$tmp_dir/actual.tsv"
diff -u expected/inventory_fixture.tsv "$tmp_dir/actual.tsv"
echo "OCAML_OPEN_INVENTORY_TEST_OK"
