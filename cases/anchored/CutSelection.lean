import PairTable

namespace WildAnchor
open Finset

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Compose a placement on the right with a change of coordinates on the
anchor edges. This permutes all possible shuffles. -/
def changeFrame (q : Shuffle I) : Shuffle I ≃ Shuffle I where
  toFun p := (p.1.trans q.1,fun i => xor (p.2 i) (q.2 (p.1 i)))
  invFun p := (p.1.trans q.1.symm,fun i => xor (p.2 i) (q.2 (q.1.symm (p.1 i))))
  left_inv := by rintro ⟨p,b⟩; apply Prod.ext <;> simp <;> ext i <;> simp
  right_inv := by rintro ⟨p,b⟩; apply Prod.ext <;> simp <;> ext i <;> simp

omit [Fintype I] [DecidableEq I] in
theorem perm_change (q p : Shuffle I) (x : Pts I) :
    perm (changeFrame q p) x=perm q (perm p x) := by
  rcases x with ⟨i,b⟩
  simp [perm,changeFrame,Bool.xor_assoc]

def inverseShuffle (q : Shuffle I) : Shuffle I :=
  (q.1.symm,fun i => q.2 (q.1.symm i))

omit [Fintype I] [DecidableEq I] in
theorem perm_inverse (q : Shuffle I) (x : Pts I) :
    perm (inverseShuffle q) x=(perm q).symm x := rfl

omit [Fintype I] [DecidableEq I] in
theorem fits_change (q p : Shuffle I) (s t : State I) :
    Fits p s (transport q t) ↔ Fits (changeFrame (inverseShuffle q) p) s t := by
  simp only [fits_iff,transport,flag_state,perm_change,perm_inverse]

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
noncomputable def losses (s : A → State I) (t : B → State I) : Finset (Shuffle I) := by
  classical exact univ.filter fun p => ∃ a b,Fits p (s a) (t b)

theorem losses_mem (s : A → State I) (t : B → State I) (p : Shuffle I) :
    p∈losses s t ↔ ∃ a b,Fits p (s a) (t b) := by classical simp [losses]

/-- Bound each color in its own anchor coordinates, then choose one
placement avoiding all of their losses. -/
theorem choose_from_losses (s : A → State I) (t : C → B → State I)
    (coords : C → Shuffle I) (price : C → Nat)
    (per : ∀ c,(losses s (t c)).card≤price c)
    (small : (∑ c,price c)<(Fintype.card I).factorial*2^(Fintype.card I)) :
    ∃ p : Shuffle I,∀ c a b,¬Fits p (s a) (transport (coords c) (t c b)) := by
  classical
  let cost (c : C) := (losses s (t c)).map (changeFrame (inverseShuffle (coords c))).symm.toEmbedding
  have card (c : C) : (cost c).card≤price c := (card_map _).le.trans (per c)
  have cnt := (card_biUnion_le (s:=univ) (t:=cost)).trans (sum_le_sum fun c _ => card c)
  have full : (univ : Finset (Shuffle I)).card=(Fintype.card I).factorial*2^Fintype.card I := by
    simp [Shuffle,Fintype.card_prod,Fintype.card_perm]
  obtain ⟨p,_,ok⟩ := exists_mem_not_mem_of_card_lt_card
    (s:=univ.biUnion cost) (t:=univ) (full ▸ cnt.trans_lt small)
  refine ⟨p,fun c a b fit => ok (mem_biUnion.mpr ⟨c,mem_univ _,?_⟩)⟩
  exact mem_map.mpr ⟨_,(losses_mem ..).mpr ⟨a,b,(fits_change ..).mp fit⟩,(changeFrame (inverseShuffle (coords c))).symm_apply_apply p⟩

end WildAnchor
