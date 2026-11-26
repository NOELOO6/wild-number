#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
src="$root/cases/k17"
source "$root/verification/native.sh"
native_module "$src/Groupings.lean"
native_module "$src/ThirdColors.lean" -lGroupings
plugins=(--plugin="$build/libGroupings.$ext" --plugin="$build/libThirdColors.$ext")
"$lean" -j "${LEAN_JOBS:-4}" "${plugins[@]}" -o "$build/Rows.olean" "$src/Rows.lean"
"$lean" "${plugins[@]}" "$src/Certificate.lean"
if [[ ! -f $build/Delete.olean ]]; then "$lean" -o "$build/Delete.olean" "$root/cases/k16/Delete.lean"; fi
"$lean" "$src/Connectivity.lean"
"$lean" "$src/Incidence.lean"
"$lean" "$src/Example.lean"
"${CXX:-c++}" -std=c++20 -O3 -Wall -Wextra -pedantic "$src/check.cpp" -o "$build/k17-check"
"$build/k17-check" "$src/prices.txt"
