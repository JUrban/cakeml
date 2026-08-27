#!/bin/sh

set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
expected_version=4.14.1
actual_version=$(ocamlc -version)

if [ "$actual_version" != "$expected_version" ]; then
  echo "OCaml version mismatch: expected $expected_version, got $actual_version" >&2
  exit 1
fi

tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/cakeml-dopen-oracle.XXXXXX")
trap 'rm -rf -- "$tmp_dir"' EXIT HUP INT TERM

tab=$(printf '\t')
passed=0

while IFS="$tab" read -r case_name outcome category expectation; do
  case "$case_name" in
    ''|'#'*) continue ;;
  esac

  source_file="$script_dir/cases/$case_name.ml"
  copied_source="$tmp_dir/$case_name.ml"
  executable="$tmp_dir/$case_name.exe"
  stdout_file="$tmp_dir/$case_name.stdout"
  stderr_file="$tmp_dir/$case_name.stderr"

  cp -- "$source_file" "$copied_source"

  case "$outcome" in
    pass)
      if ! ocamlc -o "$executable" "$copied_source" 2>"$stderr_file"; then
        echo "FAIL $case_name ($category): reference compilation failed" >&2
        sed -n '1,80p' "$stderr_file" >&2
        exit 1
      fi
      "$executable" >"$stdout_file"
      if ! diff -u "$script_dir/expected/$expectation" "$stdout_file"; then
        echo "FAIL $case_name ($category): output differs" >&2
        exit 1
      fi
      ;;
    fail)
      if ocamlc -o "$executable" "$copied_source" >"$stdout_file" 2>"$stderr_file"; then
        echo "FAIL $case_name ($category): compilation unexpectedly succeeded" >&2
        exit 1
      fi
      if ! grep -F -- "$expectation" "$stderr_file" >/dev/null; then
        echo "FAIL $case_name ($category): expected diagnostic not found" >&2
        sed -n '1,80p' "$stderr_file" >&2
        exit 1
      fi
      ;;
    *)
      echo "Invalid outcome '$outcome' for $case_name" >&2
      exit 1
      ;;
  esac

  passed=$((passed + 1))
  echo "PASS $case_name $category"
done < "$script_dir/cases.tsv"

echo "OCAML_OPEN_ORACLE_OK cases=$passed version=$actual_version"
