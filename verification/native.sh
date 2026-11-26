# Helpers for the large native_decide proofs. The caller sets lean and build.
case "$(uname -s)" in
  Darwin) ext=dylib; shared=-dynamiclib ;;
  Linux)  ext=so; shared=-shared ;;
  *) echo 'The accelerated proof replay supports Linux and macOS.' >&2; exit 2 ;;
esac
native_module() {
    local source=$1 name flags=()
    shift
    name=$(basename "$source" .lean)
    if (( $# )); then flags=(-L"$build" "$@" -Wl,-rpath,"$build"); fi
    (cd "$(dirname "$source")" &&
        "$lean" -o "$build/$name.olean" -c "$build/$name.c" "$source")
    "$(dirname "$lean")/leanc" -O3 -DLEAN_EXPORTING -fPIC "$shared" "$build/$name.c" \
        "${flags[@]}" -o "$build/lib$name.$ext"
}
