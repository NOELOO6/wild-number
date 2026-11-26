#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
jobs=${LEAN_JOBS:-2}
src="$root/cases/k15/prescribed"
native_module "$src/Prescribed.lean"
native_module "$src/Twelve.lean" -lPrescribed

named="$root/cases/k15/nine-named"
native_module "$named/NineNamed.lean" -lPrescribed
"$lean" --plugin="$build/libNineNamed.$ext" -j "$jobs" -s 65536 -o "$build/NineRows.olean" "$named/NineRows.lean"
"$lean" "$named/NineBound.lean"

last="$root/cases/k16/last-two"
native_module "$last/LastTwo.lean" -lTwelve -lPrescribed
"$lean" --plugin="$build/libLastTwo.$ext" -j "$jobs" -s 65536 -o "$build/LastTwoRows.olean" "$last/LastTwoRows.lean"
native_module "$last/SquarePair.lean" -lLastTwo -lTwelve -lPrescribed
"$lean" --plugin="$build/libSquarePair.$ext" -j "$jobs" -s 65536 -o "$build/SquareRows.olean" "$last/SquareRows.lean"
"$lean" "$last/LastTwoBound.lean"
native_module "$root/examples/SearchExample.lean"
"$lean" -s 65536 --plugin="$build/libSearchExample.$ext" --plugin="$build/libPrescribed.$ext" "$last/PrefixExample.lean"

big="$root/cases/k19/named"
native_module "$big/PairCuts19.lean"
"$lean" --plugin="$build/libPairCuts19.$ext" -j "$jobs" -s 65536 -o "$build/PairRows19.olean" "$big/PairRows19.lean"
native_module "$big/Separate19.lean" -lPairCuts19
"$lean" --plugin="$build/libSeparate19.$ext" -o "$build/SeparateRows19.olean" "$big/SeparateRows19.lean"
"$lean" "$big/Named19Bound.lean"
