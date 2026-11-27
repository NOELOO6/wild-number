import Numeric
import Lean.Elab.Term

namespace WildSieve
open Lean Elab Term

/-- Construct candidate integer tables at elaboration time. The resulting term
is a list of numerals. Each inequality is then proved by kernel reduction. -/
elab "sieveTables%(" low:num "," count:num ")" : term => do
  let cases := (List.range count.getNat).map fun i =>
    let n := low.getNat + 2*i
    (n, makeTable n (fixedSize n) (levels n))
  return toExpr cases

private def passedTable (e : Nat × Array Nat) :=
  tablePasses e.1 (fixedSize e.1) (levels e.1) e.2

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private def block0 := sieveTables%(83,4)
private theorem pass0 : block0.all passedTable=true := by decide

private def block1 := sieveTables%(91,4)
private theorem pass1 : block1.all passedTable=true := by decide

private def block2 := sieveTables%(99,4)
private theorem pass2 : block2.all passedTable=true := by decide

private def block3 := sieveTables%(107,4)
private theorem pass3 : block3.all passedTable=true := by decide

private def block4 := sieveTables%(115,4)
private theorem pass4 : block4.all passedTable=true := by decide

private def block5 := sieveTables%(123,4)
private theorem pass5 : block5.all passedTable=true := by decide

private def block6 := sieveTables%(131,4)
private theorem pass6 : block6.all passedTable=true := by decide

private def block7 := sieveTables%(139,4)
private theorem pass7 : block7.all passedTable=true := by decide

private def block8 := sieveTables%(147,4)
private theorem pass8 : block8.all passedTable=true := by decide

private def tableList := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8

private theorem checked : tableList.all passedTable=true := by
  simp only [tableList,List.all_append,pass0,pass1,pass2,pass3,pass4,pass5,pass6,pass7,pass8,Bool.and_self]

private theorem orders : tableList.map Prod.fst=(List.range 36).map (fun i => 83+2*i) := by decide

theorem medium_certificate (n : Nat) (lo : 83≤n) (hi : n≤153) (odd : n%2=1) :
    ∃ h,Cert n (fixedSize n) (levels n) h := by
  have member : n∈tableList.map Prod.fst := by
    rw [orders]
    exact List.mem_map.mpr ⟨(n-83)/2,List.mem_range.mpr (by omega),by omega⟩
  obtain ⟨⟨k,a⟩,inside,rfl⟩ := List.mem_map.mp member
  exact ⟨_,cert_of_table k _ _ a (List.all_eq_true.mp checked (k,a) inside)⟩

#print axioms medium_certificate
end WildSieve
