#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
src="$root/cases/k15/protected-colors"
if [[ ! -f $build/Teams.olean ]]; then "$lean" -o "$build/Teams.olean" "$root/cases/k15/Teams.lean"; fi
native_module "$src/Protected.lean"
native_module "$src/TwoAnchors.lean" -lProtected
plugins=(--plugin="$build/libProtected.$ext" --plugin="$build/libTwoAnchors.$ext")
"$lean" "${plugins[@]}" "$src/CheckProtected.lean"
"$lean" "${plugins[@]}" "$src/Example.lean"
"$lean" -s 65536 -j "${LEAN_JOBS:-4}" "${plugins[@]}" "$src/CheckTwo.lean"
