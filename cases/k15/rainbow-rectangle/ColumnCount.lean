import Factors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

namespace WildRectangle
open Finset
variable {V C : Type} [DecidableEq V] [DecidableEq C]

omit [DecidableEq V] in
/-- Count incidences between columns and colors by either coordinate. -/
theorem intersection_sum (P : V → Finset C) (S : Finset V) (D : Finset C) :
    (∑ x∈S,(D∩P x).card)=∑ c∈D,(S.filter (fun x => c∈P x)).card := by
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [←card_filter]
  congr 1

/-- If seven or more columns all intersect one another, three entries per
column and three occurrences per color force a seven-point triple system. -/
theorem tight_columns (P : V → Finset C) (Y : Finset V) (seven : 7≤Y.card)
    (size : ∀ y∈Y,(P y).card=3) (freq : ∀ c,(Y.filter (fun y => c∈P y)).card≤3)
    (meet : ∀ x∈Y,∀ y∈Y,x≠y → (P x ∩ P y).Nonempty) (x : V) (hx : x∈Y) :
    Y.card=7 ∧ (∀ c∈P x,(Y.filter (fun y => c∈P y)).card=3) ∧
      (∀ y∈Y,y≠x → (P x ∩ P y).card=1) := by
  let S := Y.erase x
  let w (c : C) := (S.filter (fun y => c∈P y)).card
  have sc : S.card=Y.card-1 := card_erase_of_mem hx
  have eq (c : C) (h : c∈P x) : w c+1=(Y.filter (fun y => c∈P y)).card := by
    have same : S.filter (fun y => c∈P y)=(Y.filter (fun y => c∈P y)).erase x := by ext y; simp [S,and_assoc,and_left_comm]
    have mem : x∈Y.filter (fun y => c∈P y) := mem_filter.mpr ⟨hx,h⟩
    dsimp [w]
    rw [same,card_erase_of_mem mem]
    have := card_pos.mpr ⟨x,mem⟩
    omega
  have wp (c) (hc : c∈P x) : w c≤2 := by have := eq c hc; have := freq c; omega
  have vp (y) (hy : y∈S) : 1≤(P x ∩ P y).card :=
    card_pos.mpr (meet x hx y (mem_erase.mp hy).2 (mem_erase.mp hy).1.symm)
  have vlow := sum_le_sum vp
  have whigh := sum_le_sum wp
  have count := intersection_sum P S (P x)
  change (∑ y∈S,(P x∩P y).card)=∑ c∈P x,w c at count
  have low : S.card≤∑ y∈S,(P x∩P y).card := by simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] using vlow
  have high : (∑ c∈P x,w c)≤6 := by simpa only [sum_const,nsmul_eq_mul,size x hx] using whigh
  have wc : (∑ c∈P x,w c)=∑ _∈P x,2 := by simp only [sum_const,nsmul_eq_mul,size x hx]; omega
  have vc : (∑ _∈S,1)=∑ y∈S,(P x∩P y).card := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]; omega
  refine ⟨by omega,fun c hc => ?_,fun y hy ne => ?_⟩
  · have w2 := (sum_eq_sum_iff_of_le wp).mp wc c hc
    have := eq c hc
    omega
  · exact ((sum_eq_sum_iff_of_le vp).mp vc y (mem_erase.mpr ⟨ne,hy⟩)).symm

/-- A column with a color occurring only once can collide with at most four
other columns when the two remaining colors have at most three entries each. -/
theorem companions (P : V → Finset C) (S : Finset V) (twelve : 12≤S.card) (x : V) (hx : x∈S)
    (size : (P x).card=3) (freq : ∀ c,(S.filter (fun y => c∈P y)).card≤3)
    (c : C) (cx : c∈P x) (alone : ∀ y∈S,c∈P y → y=x) :
    7≤((S.erase x).filter (fun y => Disjoint (P x) (P y))).card := by
  classical
  let E := S.erase x
  let N (d : C) := E.filter fun y => d∈P y
  have bound (d) (dx : d∈P x) : (N d).card≤2 := by
    have sub : N d⊆(S.filter (fun y => d∈P y)).erase x := fun y hy =>
      let h := mem_filter.mp hy
      mem_erase.mpr ⟨(mem_erase.mp h.1).1,mem_filter.mpr ⟨(mem_erase.mp h.1).2,h.2⟩⟩
    have n := card_le_card sub
    rw [card_erase_of_mem (mem_filter.mpr ⟨hx,dx⟩)] at n
    have := freq d
    omega
  let bad := E.filter (fun y => ¬Disjoint (P x) (P y))
  have sub : bad⊆((P x).erase c).biUnion N := by
    intro y hy
    obtain ⟨hy,h⟩ := mem_filter.mp hy
    obtain ⟨d,dx,dy⟩ := not_disjoint_iff.mp h
    have ne : d≠c := by rintro rfl; exact (mem_erase.mp hy).1 (alone y (mem_erase.mp hy).2 dy)
    exact mem_biUnion.mpr ⟨d,mem_erase.mpr ⟨ne,dx⟩,mem_filter.mpr ⟨hy,dy⟩⟩
  have cap := ((card_le_card sub).trans card_biUnion_le).trans (sum_le_sum (s:=(P x).erase c)
    (fun d hd => bound d (mem_erase.mp hd).2))
  rw [sum_const,nsmul_eq_mul,card_erase_of_mem cx,size] at cap
  have all := card_sdiff_add_card_eq_card (show bad⊆E from filter_subset _ _)
  have rest : E \ bad=E.filter (fun y => Disjoint (P x) (P y)) := by ext y; simp [bad]; tauto
  rw [rest] at all
  change 7≤(E.filter (fun y => Disjoint (P x) (P y))).card
  have es : E.card=S.card-1 := card_erase_of_mem hx
  omega
end WildRectangle
