import GraphSieve
namespace WildSieve.AnchorPacking
open Finset WildExact

variable {V : Type} [DecidableEq V]

/-- The possible six-point sides obtained by choosing two triples. -/
def halfSides (D : Blocks V) := (D.powersetCard 2).image vertices

theorem side_of_seal [Fintype V] {D : Layout (univ : Finset V)} {X : Finset V}
    (sx : X.card=6) (hit : D∈sealEvent X) : X∈halfSides D.val := by
  obtain ⟨M,md⟩ := mem_seal.mp hit
  have sz := M.property.1.card_vertices
  rw [M.property.2,sx] at sz
  exact mem_image.mpr ⟨M.val,mem_powersetCard.mpr ⟨md,by omega⟩,M.property.2⟩

theorem triple_of_seal [Fintype V] {D : Layout (univ : Finset V)} {T : Finset V}
    (sz : T.card=3) (hit : D∈sealEvent T) : T∈D.val := by
  obtain ⟨M,md⟩ := mem_seal.mp hit
  have card := M.property.1.card_vertices
  rw [M.property.2,sz] at card
  obtain ⟨Q,hq⟩ := card_eq_one.mp (show M.val.card=1 by omega)
  have eq : Q=T := by simpa only [hq,vertices_singleton] using M.property.2
  exact md (by simp [hq,eq])

private theorem weighted_cover {I A : Type} [Fintype I] [DecidableEq A] (S : Finset A)
    (weight : I → Nat) (touch : I → A → Prop) [∀ i x,Decidable (touch i x)]
    (cap : Nat) (price : ∀ x∈S,(∑ i,if touch i x then weight i else 0)≤cap) :
    (∑ i,if ∃ x∈S,touch i x then weight i else 0)≤S.card*cap := by
  classical
  calc
    _ ≤ ∑ i,∑ x∈S,if touch i x then weight i else 0 := by
      apply sum_le_sum
      intro i _
      split
      next h =>
        obtain ⟨x,hx,yes⟩ := h
        simpa only [if_pos yes] using single_le_sum (s:=S) (f:=fun x => if touch i x then weight i else 0)
          (fun _ _ => Nat.zero_le _) hx
      next => exact Nat.zero_le _
    _ = ∑ x∈S,∑ i,if touch i x then weight i else 0 := sum_comm
    _ ≤ ∑ _∈S,cap := sum_le_sum price
    _ = _ := by simp [nsmul_eq_mul]

local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

/-- In each layout, the four open triples must pass the two tests involving the
anchor. The other three cuts are complementary pairs of six-point sides.
Every coloring can mark at most 96 individual six-point sides. -/
theorem anchor_wins {I : Type} [Fintype I] (F : Factor (Fin 16) (Fin 15))
    (B : Finset (Fin 16)) (root : Fin 16) (hr : root∈B) (bs : B.card=4) (rain : Rainbow F B)
    (row : I → Layout (univ : Finset (Free B))) (weight : I → Nat)
    (extra : Finset (Finset (Free B))) (a b : Nat)
    (singles : ∀ i T,T∈(row i).val → T∈badScopes F B root 3 4 1 → T∈extra)
    (one : ∀ T∈extra,(∑ i,if T∈(row i).val then weight i else 0)≤a)
    (two : ∀ X,(∑ i,if X∈halfSides (row i).val then weight i else 0)≤b)
    (room : extra.card*a+96*b<∑ i,weight i) :
    ∃ i,∀ j∈shortLevels∪longLevels 4,∀ X∈badScopes F B root 3 4 j,row i∉sealEvent X := by
  classical
  let E := badScopes F B root 3 4 2
  have ws : Bᶜ.card=12 := by rw [card_compl,Fintype.card_fin,bs]
  have bound : E.card≤96 := by
    apply (bad_scope_count F B root 3 4 hr bs ws rain 2).trans
    decide
  have c1 := weighted_cover extra weight (fun i T => T∈(row i).val) a one
  have c2 := weighted_cover E weight (fun i X => X∈halfSides (row i).val) b (fun X _ => two X)
  by_contra! all
  have per (i : I) : weight i ≤ (if ∃ T∈extra,T∈(row i).val then weight i else 0) +
      (if ∃ X∈E,X∈halfSides (row i).val then weight i else 0) := by
    obtain ⟨j,hj,X,hx,hit⟩ := all i
    obtain ⟨D,_,xd⟩ := (mem_gather _ _ X).mp hx
    have sz := (pull_mem.mp xd).1
    have lev : j=1 ∨ j=2 := by
      have eq : shortLevels∪longLevels 4={1,2} := by decide
      simpa only [eq,mem_insert,mem_singleton] using hj
    rcases lev with rfl|rfl
    · have member := triple_of_seal sz hit
      rw [if_pos (show ∃ T∈extra,T∈(row i).val from ⟨X,singles i X member hx,member⟩)]
      omega
    · rw [if_pos (show ∃ X∈E,X∈halfSides (row i).val from ⟨X,hx,side_of_seal sz hit⟩)]
      omega
  have total := sum_le_sum (s:=univ) (fun i _ => per i)
  rw [sum_add_distrib] at total
  exact (not_lt_of_ge (total.trans (Nat.add_le_add c1 (c2.trans (Nat.mul_le_mul_right _ bound))))) room

end WildSieve.AnchorPacking
