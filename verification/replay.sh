#!/usr/bin/env bash
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
lean_bin=$(command -v "${LEAN:-lean}")
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
fi
if [[ $mode == k15 || $mode == all ]]; then
    "$lean_bin" -o "$build/CheckBase.olean" "$root/cases/k15/CheckBase.lean"
    for file in Cyclic15 Near15 Teams HardRepair LineTrap; do "$lean_bin" "$root/cases/k15/$file.lean"; done
    python3 "$root/cases/k15/verify_k15.py"
    python3 "$root/cases/k15/check_example.py"
fi
if [[ $mode == k16 || $mode == all ]]; then
    "$lean_bin" "$root/cases/k16/Untouched16.lean"
    "$lean_bin" "$root/cases/k16/Perfect16.lean"
fi
