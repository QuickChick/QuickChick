#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
demo_file="$repo_dir/slides/testing_theorems_svg_storyboard_v2/testing_theorems_svg_storyboard_v2/demo/STLCBugDemo.v"
demo_tmp="$(mktemp -d /tmp/quickchick-stlc-demo.XXXXXX)"
trap 'rm -rf "$demo_tmp"' EXIT
output_vo="$demo_tmp/STLCBugDemo.vo"
output_log="$demo_tmp/coqc.log"

cd "$repo_dir"
if ! opam exec --switch=rocq-rewrite -- \
  coqc \
      -R _build/default/src QuickChick \
      -I _build/default/plugin \
      -noglob \
      -o "$output_vo" \
      "$demo_file" >"$output_log" 2>&1; then
  cat "$output_log"
  exit 1
fi

sed -n '/Theorem Schedule:/,$p' "$output_log" \
  | sed -e '/^Compiling inductive schedule:/d' \
        -e '/^Pieces:/d' \
        -e 's/(Coq.Init.Datatypes.nil typ)/[]/g' \
  | awk 'NF { blank = 0; print; next } !blank { print; blank = 1 }'
