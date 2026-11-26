#!/usr/bin/env bash
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
lean_bin=$(realpath "$(command -v "${LEAN:-lean}")")
cd "$root"
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
mode=${1:-all}
case "$mode" in all|k13|k15|k16) ;; *) echo "Usage: $0 [all|k13|k15|k16]" >&2; exit 2;; esac
"$lean_bin" --version
if [[ $mode == k13 || $mode == all ]]; then
    cp "$root/cases/k13/CertifiedNine.lean" "$build/"
    for ext in cnf lrat; do gzip -dc "$root/cases/k13/ninesym.$ext.gz" > "$build/ninesym.$ext"; done
    "$lean_bin" "$build/CertifiedNine.lean"
    python3 "$root/cases/k13/make_k13_formula.py" "$build/regenerated.cnf"
    cmp "$build/regenerated.cnf" "$build/ninesym.cnf"
fi
if [[ $mode != k13 ]]; then
    "$lean_bin" -o "$build/Delete.olean" "$root/cases/k16/Delete.lean"
    "$lean_bin" -o "$build/Teams.olean" "$root/cases/k15/Teams.lean"
fi
if [[ $mode != k13 ]]; then
    "$lean_bin" -s 65536 -o "$build/ThreeExceptions.olean" "$root/cases/k16/three-exceptions/ThreeExceptions.lean"
    "$lean_bin" -s 65536 "$root/cases/k16/three-exceptions/EveryDeletion.lean"
fi
if [[ $mode == k15 || $mode == all ]]; then
    "$lean_bin" -s 65536 "$root/cases/k15/five-colors/Completion.lean"
    "$lean_bin" -o "$build/CheckBase.olean" "$root/cases/k15/CheckBase.lean"
    "$lean_bin" -s 65536 -o "$build/Endgame.olean" "$root/cases/k15/Endgame.lean"
    "$lean_bin" -s 65536 -o "$build/Counting.olean" "$root/cases/k15/counting/Counting.lean"
    "$lean_bin" -s 65536 "$root/cases/k15/counting/Squares.lean"
    cp "$root/cases/k15/endgame/BlockCatalogue.lean" "$build/"
    gzip -dc "$root/cases/k15/endgame/graphs8.txt.gz" > "$build/graphs8.txt"
    gzip -dc "$root/cases/k15/endgame/cert43.tree.gz" > "$build/cert.tree"
    gzip -dc "$root/cases/k15/endgame/cert43.blocks.gz" > "$build/cert.blocks"
    "$lean_bin" --root="$build" -s 65536 -o "$build/BlockCatalogue.olean" "$build/BlockCatalogue.lean"
    "$lean_bin" -s 65536 "$root/cases/k15/FirstTriple.lean"
    for file in Completion Score39 Sharp40; do
        "$lean_bin" -s 65536 "$root/cases/k15/endgame/$file.lean"
    done
    cp "$root/cases/k15/endgame/CertifiedEndgame.lean" "$build/"
    for ext in cnf lrat; do gzip -dc "$root/cases/k15/endgame/end38.$ext.gz" > "$build/end38.$ext"; done
    "$lean_bin" -s 65536 "$build/CertifiedEndgame.lean"
    python3 "$root/cases/k15/endgame/make_formula.py" "$build/regenerated38.cnf"
    cmp "$build/regenerated38.cnf" "$build/end38.cnf"
    "$lean_bin" -o "$build/HalfSplits.olean" "$root/cases/k15/HalfSplits.lean"
    for file in TwoCuts FiveTeams ThreeTeams Five Cyclic15 Near15 Trade HardRepair LineTrap FourChanges Seven; do "$lean_bin" "$root/cases/k15/$file.lean"; done
    python3 "$root/cases/k15/verify_k15.py"
    python3 "$root/cases/k15/check_example.py"
    python3 "$root/cases/k15/check_four_changes.py"
    python3 "$root/cases/k15/check_seven.py"
fi
if [[ $mode == k16 || $mode == all ]]; then
    "$lean_bin" -s 65536 "$root/cases/k16/four-colors/FourColors.lean"
    "$lean_bin" "$root/cases/k16/Untouched16.lean"
    "$lean_bin" "$root/cases/k16/Perfect16.lean"
    "$lean_bin" -s 65536 "$root/cases/k16/SevenSet.lean"
    "$lean_bin" -s 65536 "$root/cases/k16/SevenMoments.lean"
fi
