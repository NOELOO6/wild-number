import ProfileBills30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) sideEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

def sideZone (S : Finset V) (v : V) : Fin 4 := if v∈S then 2 else 3

theorem side_zones (S : Finset V) :
    zone (sideZone S) 0=∅ ∧ zone (sideZone S) 1=∅ ∧
      zone (sideZone S) 2=S ∧ zone (sideZone S) 3=Sᶜ := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext x <;> by_cases h : x∈S <;> simp [zone,sideZone,h]

theorem side_signature (F : Factor V C) (c : C) (S : Finset V) (small : S.card≤15) :
    signatureOf F c (sideZone S)=sideSignature S.card (Inside F c S) := by
  obtain ⟨a,b,l,r⟩ := side_zones S
  have row (U : Finset V) : 2*Inside F c U+links F c U Uᶜ=U.card := by
    have h := links_union F c U U Uᶜ disjoint_compl_right
    rw [show U∪Uᶜ=univ by ext x; simp,links_self] at h
    simpa [links] using h.symm
  have h := row S
  have hc := row Sᶜ
  rw [compl_compl,links_symm F c Sᶜ S,card_compl,Fintype.card_fin] at hc
  have cross : links F c S Sᶜ=S.card-2*Inside F c S := by omega
  have rest : Inside F c Sᶜ=15-S.card+Inside F c S := by omega
  have iz : Inside F c ∅=0 := by simp [Inside,lowerEnds]
  have lz (U : Finset V) : links F c ∅ U=0 := by simp [links]
  simp only [signatureOf,a,b,l,r,sideSignature,cross,rest,iz,lz]

theorem count_side_left (S Q : Finset V) :
    (Q.val.map (sideZone S)).count 2=(Q∩S).card := by
  rw [Multiset.count_map]
  change (Q.filter (fun x => (2 : Fin 4)=sideZone S x)).card=_
  congr 1
  ext x
  by_cases h : x∈S <;> simp [sideZone,h]

theorem count_side_right (S Q : Finset V) :
    (Q.val.map (sideZone S)).count 3=(Q \ S).card := by
  rw [Multiset.count_map]
  change (Q.filter (fun x => (3 : Fin 4)=sideZone S x)).card=_
  congr 1
  ext x
  by_cases h : x∈S <;> simp [sideZone,h]

theorem labeled_first (F : Factor V C) (c : C) (L : Finset V) (size : L.card=12) (t : Fin 3) :
    (∑ Q∈candidates F c ∅ univ 6,
        if (Q∩L).card=6-3*t.val then ((localSeal univ L∩localSeal univ Q).card : ℚ) else 0) =
      first t (Inside F c L)*(layoutWays 12*layoutWays 18 : Nat) := by
  let i : Fin 7 := ⟨Inside F c L,by have := (inside_window F c L).2; omega⟩
  have sg := side_signature F c L (by omega)
  rw [size] at sg
  have eq := first_completions_sum F c (sideZone L) t i sg
  rw [Nat.cast_sum] at eq
  refine Eq.trans (sum_congr rfl (fun Q _ => ?_)) eq
  rw [givenSide,count_side_left,count_side_right]
  split
  · rw [joint_seal_ways _ _ _ (subset_univ _) (subset_univ _),size,card_sdiff (subset_univ _),card_univ,Fintype.card_fin,size]
  · simp

theorem duplicate_anchors (F : Factor V C) (c : C) (S : Finset V) (size : S.card=6) (t : Fin 3) :
    (((candidates F c ∅ univ 12).filter (fun Q => (Q∩S).card=6-3*t.val)).card : ℚ) *
      factor 12 18 t=duplicateWeight t (Inside F c S)*(Nat.choose 15 6) := by
  let i : Fin 4 := ⟨Inside F c S,by have := (inside_window F c S).2; omega⟩
  have sg := side_signature F c S (by omega)
  rw [size] at sg
  have eq := duplicate_completions_sum F c (sideZone S) t i sg
  simpa only [chosenSide,count_side_left,sum_boole] using eq

end WildSieve.Thirty.Graph
