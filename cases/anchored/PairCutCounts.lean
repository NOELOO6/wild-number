import DisjointCuts
import IncidenceCredit

namespace WildAnchor.K30
open Finset
open scoped Classical
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def mark (q : DoubleCut) (x : Fin 10) : Label :=
  if x∈left q then 1 else if x∈right q then 2 else 0

private theorem mark_test : ∀ q : DoubleCut, ∀ x : Fin 10,
    (mark q x=1 ↔ x∈left q) ∧ (mark q x=2 ↔ x∈right q) := by native_decide

def source3 (q : DoubleCut) : Colors3 (Fin 15) :=
  fun i => (mark q (tag (i,false)),mark q (tag (i,true)))

abbrev Pick := Finset (Fin 15) × Finset (Fin 15)
def picks : Finset Pick :=
  let triples := (univ : Finset (Fin 15)).powersetCard 3
  (triples ×ˢ triples).filter fun ab => Disjoint ab.1 ab.2

def code (k : Pick) (i : Fin 15) : Label := if i∈k.1 then 1 else if i∈k.2 then 2 else 0

private theorem code_eq (k : Pick) (hk : k∈picks) (i : Fin 15) :
    (code k i=1 ↔ i∈k.1) ∧ (code k i=2 ↔ i∈k.2) := by
  have dis := (mem_filter.mp hk).2
  by_cases a : i∈k.1
  · have b := disjoint_left.mp dis a
    simp [code,a,b]
  · by_cases b : i∈k.2 <;> simp [code,a,b]

private theorem unique_code {k l : Pick} (hk : k∈picks) (hl : l∈picks) (eq : code k=code l) : k=l := by
  apply Prod.ext
  · ext i; rw [←(code_eq k hk i).1,←(code_eq l hl i).1,eq]
  · ext i; rw [←(code_eq k hk i).2,←(code_eq l hl i).2,eq]

def row3 (next : Equiv.Perm (Fin 15)) (k : Pick) : Colors3 (Fin 15) :=
  fun i => (code k i,code k (next.symm i))

private def read3 (s : Colors3 (Fin 15)) (z : Point 15) : Label :=
  if z.2 then (s z.1).2 else (s z.1).1

private theorem three_at {p : Shuffle (Fin 15)} {s t : Colors3 (Fin 15)} (h : fitsThree p s t)
    (z : Point 15) : read3 s z=read3 t (perm p z) := by
  obtain ⟨i,b⟩ := z
  have e := h i
  change turnPair (p.2 i) (s i)=t (p.1 i) at e
  cases b <;> cases o : p.2 i <;> simp_all [perm,read3,turnPair]
  · exact congrArg Prod.snd e
  · exact congrArg Prod.fst e

private theorem placed_code {p : Shuffle (Fin 15)} {q next k}
    (h : fitsThree p (source3 q) (row3 next k)) (i : Fin 15) :
    mark q (placed p i false)=code k i ∧ mark q (placed p (next i) true)=code k i := by
  have eq (v : Point 15) := three_at h ((perm p).symm v)
  have a := eq (i,false)
  have b := eq (next i,true)
  rw [Equiv.apply_symm_apply] at a b
  have src (w : Point 15) : read3 (source3 q) w=mark q (tag w) := by
    rcases w with ⟨j,z⟩;cases z <;> rfl
  rw [src] at a b
  exact ⟨a,by simpa only [read3,row3,if_true,Equiv.symm_apply_apply] using b⟩

private theorem double_of_fit {p q next k} (fit : fitsThree p (source3 q) (row3 next k)) :
    both p next q := by
  have e (i) := (placed_code fit i).1.trans (placed_code fit i).2.symm
  constructor <;> intro i
  · rw [←(mark_test q _).1,←(mark_test q _).1,e]
  · rw [←(mark_test q _).2,←(mark_test q _).2,e]

private theorem fits_unique {p q next k l} (hk : k∈picks) (hl : l∈picks)
    (a : fitsThree p (source3 q) (row3 next k)) (b : fitsThree p (source3 q) (row3 next l)) : k=l :=
  unique_code hk hl (funext fun i => (placed_code a i).1.symm.trans (placed_code b i).1)

theorem double_lower (next : Equiv.Perm (Fin 15)) :
    (∑ q : DoubleCut,∑ k∈picks,priceThree (source3 q) (row3 next k)) ≤
      ∑ p : Shuffle (Fin 15),(doubles p next).card := by
  classical
  have bound (q : DoubleCut) : (∑ k∈picks,priceThree (source3 q) (row3 next k)) ≤
      (univ.filter fun p => both p next q).card :=
    lower_from_disjoint picks (fun k p => fitsThree p (source3 q) (row3 next k)) (fun p => both p next q)
      _ (fun k => three_price_le (source3 q) (row3 next k))
      (fun k hk l hl _ a b => fits_unique hk hl a b) (fun _ _ _ => double_of_fit)
  apply (sum_le_sum fun q _ => bound q).trans_eq
  exact count_by_outcome (fun q p => both p next q)

noncomputable def binaryLoss (next : Equiv.Perm (Fin 15)) :=
  losses (groupSide tag (r:=tag root)) (fun b : Mask 15 => row next (bits b))

private theorem closed_mem (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) (a : Side) :
    a∈closedSides p next ↔ ClosedBy p next a.val := by
  change a∈univ.filter (fun a : Side => ClosedBy p next a.val) ↔ _
  simp only [mem_filter,mem_univ,true_and]

private theorem loss_iff (next : Equiv.Perm (Fin 15)) (p : Shuffle (Fin 15)) :
    p∈binaryLoss next ↔ (closedSides p next).Nonempty := by
  rw [binaryLoss,losses_mem]
  constructor
  · rintro ⟨a,b,fit⟩
    exact ⟨a,(closed_mem p next a).mpr ((closed_iff p next a).mpr ⟨b,fit⟩)⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(closed_iff p next a).mp ((closed_mem p next a).mp ha)⟩

private theorem side_total (next : Equiv.Perm (Fin 15)) (a : Side) :
    (univ.filter fun p => ClosedBy p next a.val).card≤
      ∑ b : Mask 15,price (groupSide tag a) (row next (bits b)) :=
  loss_upper (fun b p => Fits p (groupSide tag a) (row next (bits b))) (fun p => ClosedBy p next a.val)
    _ (fun p => (closed_iff p next a).mp) (fun b => fiber_price (groupSide tag a) (row next (bits b)))

private theorem total_closed (next : Equiv.Perm (Fin 15)) :
    (∑ p : Shuffle (Fin 15),(closedSides p next).card)=
      ∑ a : Side,(univ.filter fun p => ClosedBy p next a.val).card :=
  count_by_outcome fun p (a : Side) => ClosedBy p next a.val

/-- The binary union bound pays for a shuffle at least once and pays an
additional time for every disjoint closed pair of two-group cuts. -/
theorem corrected_bound (next : Equiv.Perm (Fin 15)) :
    (binaryLoss next).card+(∑ q : DoubleCut,∑ k∈picks,priceThree (source3 q) (row3 next k)) ≤
      ∑ a : Side,∑ b : Mask 15,price (groupSide tag a) (row next (bits b)) := by
  have total := occupied_credit (fun p => closedSides p next) (binaryLoss next)
    (fun p => (doubles p next).card) (loss_iff next) (fun p => row_credit p next)
  rw [total_closed] at total
  exact ((Nat.add_le_add_left (double_lower next) _).trans total).trans
    (sum_le_sum fun a _ => side_total next a)

end WildAnchor.K30
