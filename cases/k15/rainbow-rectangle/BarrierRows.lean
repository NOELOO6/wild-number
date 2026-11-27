import RowPalettes
namespace WildRectangle
open Finset
variable {V C : Type} [DecidableEq V] [DecidableEq C] [Fintype V]

omit [DecidableEq V] in
private theorem rows_image (L : Rows V C) (a v : V) (X : Finset V) (vx : v∈X) :
    (rowSet L a X).image (fun d => L.row d v)⊆X.image (L.row a) := by
  intro k hk
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hk
  exact (mem_filter.mp hd).2 ▸ (mem_image.mpr ⟨v,vx,rfl⟩ : L.row d v∈X.image (L.row d))

omit [DecidableEq V] in
private theorem rows_size (L : Rows V C) (a : V) (X : Finset V) (ne : X.Nonempty) :
    (rowSet L a X).card≤X.card := by
  obtain ⟨v,hv⟩ := ne
  have n := card_le_card (rows_image L a v X hv)
  rwa [card_image_of_injective _ (L.column v),card_image_of_injective _ (L.row a).injective] at n

private theorem shared_rows (L : Rows V C) (a : V) (X Y : Finset V) (pos : (X∩Y).Nonempty)
    (xs : (rowSet L a X).card=X.card) (ys : (rowSet L a Y).card=Y.card) :
    (rowSet L a X∩rowSet L a Y).card=(X∩Y).card := by
  obtain ⟨v,mem⟩ := pos
  let f (d : V) := L.row d v
  have full (S : Finset V) (hv : v∈S) (sz : (rowSet L a S).card=S.card) :
      (rowSet L a S).image f=S.image (L.row a) := eq_of_subset_of_card_le (rows_image L a v S hv) (by
    rw [card_image_of_injective _ (L.row a).injective,card_image_of_injective _ (L.column v),sz])
  have h1 := full X (mem_inter.mp mem).1 xs
  have h2 := full Y (mem_inter.mp mem).2 ys
  rw [←card_image_of_injective _ (show Function.Injective f from L.column v),image_inter _ _ (L.column v),
    h1,h2,←image_inter _ _ (L.row a).injective,card_image_of_injective _ (L.row a).injective]

/-- At most eleven rows, including the two prescribed rows, belong to any
of the seven-column obstructions. -/
theorem barrier_union (L : Rows V C) (a b : V) (ab : a≠b) (U : Finset V) (cap : U.card≤12)
    (Q : Finset (Finset V)) (each : ∀ X∈Q,Seven (transition L a b) U X ∧ a∈rowSet L a X ∧ b∈rowSet L a X) :
    (Q.biUnion (rowSet L a)).card≤11 := by
  have inj := (transition L a b).injective
  have atMost := at_most_two inj U cap Q fun X hx => (each X hx).1
  have size X (hx : X∈Q) : (rowSet L a X).card≤7 := by
    have card := (each X hx).1.card
    exact (rows_size L a X (card_pos.mp (by omega))).trans_eq card
  by_cases two : Q.card=2
  · obtain ⟨X,Y,ne,eq⟩ := card_eq_two.mp two
    have x : X∈Q := by simp [eq]
    have y : Y∈Q := by simp [eq]
    have xs := size X x
    have ys := size Y y
    have pair : ({a,b} : Finset V)⊆rowSet L a X∩rowSet L a Y :=
      insert_subset (mem_inter.mpr ⟨(each X x).2.1,(each Y y).2.1⟩)
        (singleton_subset_iff.mpr (mem_inter.mpr ⟨(each X x).2.2,(each Y y).2.2⟩))
    have common := card_le_card pair
    simp [ab] at common
    simp only [eq,biUnion_insert,singleton_biUnion]
    have total := card_union_add_card_inter (rowSet L a X) (rowSet L a Y)
    by_cases full : (rowSet L a X).card=7 ∧ (rowSet L a Y).card=7
    · have overlap := (seven_overlap inj cap (each X x).1 (each Y y).1 ne).1
      have e := shared_rows L a X Y (card_pos.mp (by omega)) (full.1.trans (each X x).1.card.symm)
        (full.2.trans (each Y y).1.card.symm)
      omega
    · omega
  · have bound := card_biUnion_le (s:=Q) (t:=rowSet L a)
    have e := sum_le_sum size
    rw [sum_const,nsmul_eq_mul,Nat.cast_id] at e
    omega
end WildRectangle
