#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
src="$root/cases/k15/pair-cuts"
native_module "$root/cases/k15/prescribed/Prescribed.lean"
native_module "$src/PairCutCheck15.lean" -lPrescribed
for file in RootRows15 SquareRows15 ClearRows15 RootFourRows15 PairCutAccounting15; do
    "$lean" --root="$root" -j1 "--plugin=$build/libPairCutCheck15.$ext" -s 65536 -o "$build/$file.olean" "$src/$file.lean"
done
