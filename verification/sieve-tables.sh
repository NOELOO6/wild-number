# Compile each exact arithmetic certificate in a separate Lean process.
# KernelTables verifies that the resulting list contains the full interval.
check_sieve_tables() {
    "$lean" -j1 --root="$root" -s 65536 -o "$build/OrderTable.olean" "$root/cases/sieve/OrderTable.lean"
    local n name
    local orders=()
    local index="$build/CheckedMediumOrders.lean"
    : > "$index"
    for ((n=83; n<=153; n+=2)); do
        name="SieveOrder$n"
        cat > "$build/$name.lean" <<EOF
import OrderTable
namespace WildSieve
private def candidate$n := sieveTable%($n)
private theorem passed$n : tablePasses $n (fixedSize $n) (levels $n) candidate$n=true := by decide +kernel
def checkedOrder$n : CheckedOrder := ⟨$n,candidate$n,passed$n⟩
end WildSieve
EOF
        "$lean" -j1 --root="$build" -s 65536 -o "$build/$name.olean" "$build/$name.lean"
        printf 'import %s\n' "$name" >> "$index"
        orders+=("checkedOrder$n")
    done
    (IFS=,; printf '\nnamespace WildSieve\ndef checkedMediumOrders := [%s]\nend WildSieve\n' "${orders[*]}") >> "$index"
    "$lean" -j1 --root="$build" -s 65536 -o "$build/CheckedMediumOrders.olean" "$index"
}
