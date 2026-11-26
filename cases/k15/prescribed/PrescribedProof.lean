import PrescribedRows
import Incidence
namespace Prescribed
set_option interpreter.prefer_native true
set_option maxRecDepth 100000

def tablesOK (fixed : Bool) :=
  let rs := read fixed
  let minGain : Int := if fixed then 157642 else 2706590
  (Array.range rs.size).all fun i =>
    minGain ≤ rs[i]!.gain && (Array.range rs.size).all fun j =>
      (Array.range rs.size).all fun k =>
        let t := fun x y z : Nat => rs[x]!.transfer[y]![z]!
        t i j k == t i k j && t i j k+t j i k+t k i j ≤ 0
theorem verified_tables : tablesOK true = true ∧ tablesOK false = true := by native_decide

def two (x : Nat) := x*(x-1)/2
def three (x : Nat) := x*(x-1)*(x-2)/6
def safe (x : Nat) : Int := if x=0 then 1 else 0
def total {α : Type} (xs : List α) (f : α → Int) := (xs.map f).sum

theorem cubic (xs : List (Fin 16)) :
    12*((xs.length : Int)-total xs (fun x => x.val))+10*total xs (fun x => two x)-
    6*total xs (fun x => three x) ≤ 12*total xs (fun x => safe x) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have h := (show ∀ y : Fin 16, 12*(1-(y.val : Int))+10*(two y : Int)-
      6*(three y : Int) ≤ 12*safe y from by decide) x
    simp only [total,List.map_cons,List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one] at *
    omega

/-- Sum three local inequalities for each named triple. The transfer terms
are charged once in each of the three possible orders. -/
structure Bill where
  hit : Int
  charge : Int
  i : Nat
  j : Nat
  k : Nat

def fee (fixed : Bool) (i j k : Nat) := (read fixed)[i]!.transfer[j]![k]!

theorem sum_bills (fixed : Bool) (xs : List Bill)
    (valid : ∀ v ∈ xs, v.i < (read fixed).size ∧ v.j < (read fixed).size ∧ v.k < (read fixed).size)
    (localBound : ∀ v ∈ xs, 6*v.hit ≤ v.charge+fee fixed v.i v.j v.k+
       fee fixed v.j v.i v.k+fee fixed v.k v.i v.j) :
    6*total xs Bill.hit ≤ total xs Bill.charge := by
  have hh : tablesOK fixed = true := by
    cases fixed with
    | false => exact verified_tables.2
    | true => exact verified_tables.1
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have h := localBound x (by simp)
    obtain ⟨i,j,k⟩ := valid x (by simp)
    have a := Array.all_eq_true_iff_forall_mem.mp hh _ (Array.mem_range.mpr i)
    have b := Array.all_eq_true_iff_forall_mem.mp (Bool.and_eq_true_iff.mp a).2 _ (Array.mem_range.mpr j)
    have c := (Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp b _
      (Array.mem_range.mpr k))).2
    have cancel : fee fixed x.i x.j x.k + fee fixed x.j x.i x.k + fee fixed x.k x.i x.j ≤ 0 := by
      simpa [fee] using c
    have rest := ih (fun v hv => valid v (by simp [hv])) (fun v hv => localBound v (by simp [hv]))
    simp only [total,List.map_cons,List.sum_cons] at *
    omega

/-- The complete row inequalities, after summing over the remaining thirteen
colors in each pair account, imply a positive number of full successes for
the named colors. The incidence theorem applies to any failure relation. -/
theorem many_named (fixed : Bool) (xs : List (Fin 16)) (bills : List Bill)
    (len : xs.length = if fixed then 1401400 else 22422400)
    (one : total xs (fun x => x.val) = if fixed then 11*191800 else 13*3068800)
    (threeSum : total xs (fun x => three x) = total bills Bill.hit)
    (valid : ∀ v ∈ bills, v.i < (read fixed).size ∧ v.j < (read fixed).size ∧ v.k < (read fixed).size)
    (localBound : ∀ v ∈ bills, 6*v.hit ≤ v.charge+fee fixed v.i v.j v.k+
       fee fixed v.j v.i v.k+fee fixed v.k v.i v.j)
    (accounts : total bills Bill.charge ≤ 10*total xs (fun x => two x) -
      (if fixed then 55*157642 else 78*2706590)) :
    (if fixed then 14126 else 120835 : Int) ≤ total xs (fun x => safe x) := by
  have h := cubic xs
  have b := sum_bills fixed bills valid localBound
  rw [len,one,threeSum] at h
  cases fixed <;> simp only [Bool.false_eq_true,if_false,if_true,Int.reduceNeg,Int.reduceMul] at * <;> omega
#print axioms many_named
end Prescribed
