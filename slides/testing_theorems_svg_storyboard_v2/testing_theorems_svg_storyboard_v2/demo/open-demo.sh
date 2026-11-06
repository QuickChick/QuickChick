#!/usr/bin/env bash
set -euo pipefail

demo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd "$demo_dir/../../../.." && pwd)"
demo_file="$demo_dir/STLCBugDemo.v"
opam_switch="${QUICKCHICK_DEMO_SWITCH:-rocq-rewrite}"

command -v opam >/dev/null 2>&1 || {
  printf 'error: opam is not installed or is not on PATH\n' >&2
  exit 1
}

# Emacs and the Rocq process it starts must share the selected opam environment.
eval "$(opam env --switch="$opam_switch" --set-switch)"

command -v emacs >/dev/null 2>&1 || {
  printf 'error: emacs is not available in the %s opam environment\n' "$opam_switch" >&2
  exit 1
}

export QUICKCHICK_DEMO_FILE="$demo_file"
cd "$repo_dir"

exec emacs \
  --eval '(setq create-lockfiles nil)' \
  --no-splash \
  --name QuickChick-Demo \
  --title 'QuickChick STLC Demo' \
  --load "$demo_dir/presenter.el" \
  "$demo_file"
