#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 4 ]]; then
  echo >&2 "Usage: $0 <fname.agda> <interaction point index from 0> <ser.context> <tactic string>"
  exit 1
fi

fname=$(realpath "$1")
pointidx="$2"
viafile=$(realpath "$3")
tactics="$4"

cd "$(dirname "$0")"

if [[ "$fname" -nt "$viafile" ]]; then
  cabal run arith-solver -- -ctx "$fname" "$pointidx" "$viafile"
fi

cabal run arith-solver -- -prove "$viafile" "$tactics" | less
