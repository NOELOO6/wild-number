import FrozenStats

namespace WildSieve
open Finset

structure CutRow where
  colors : Nat
  forced : Nat
  pairs : Nat
deriving DecidableEq, Repr

/-- The three possible locations of the unique internal edge of a color
admitting the cut: inside D, inside the other frozen points, or absent. -/
def rowData (n N b d : Nat) (i : Fin 3) : CutRow :=
  if i=0 then ⟨d.choose 2,d-2,(N-(b-2))/2⟩
  else if i=1 then ⟨(b-d).choose 2,d,(N-(b-2))/2⟩
  else ⟨n-b.choose 2,d,(N-b)/2⟩

def rowAll (r : CutRow) (s u : Nat) : Nat :=
  if r.forced ≤ s ∧ (s-r.forced)%2=0 then
    Nat.fast_choose (min r.pairs ((u-r.forced)/2)) ((s-r.forced)/2)
  else 0

def rowSpecial (r : CutRow) (s u : Nat) := if r.forced=0 then 0 else rowAll r s u

def rowRegular (r : CutRow) (s u : Nat) : Nat :=
  let k := (s-r.forced)/2
  let pool := min r.pairs ((u-r.forced)/2)
  if r.forced ≤ s ∧ (s-r.forced)%2=0 ∧ 0<k ∧ 0<pool then
    Nat.fast_choose (pool-1) (k-1)
  else 0

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

def classColors (F : Factor A C) (B D : Finset A) (i : Fin 3) :=
  if i=0 then univ.filter (fun c => 0<Inside F c D)
  else if i=1 then univ.filter (fun c => 0<Inside F c (B \ D))
  else univ.filter (fun c => Inside F c B=0)

omit [Fintype A] [Fintype C] in
private theorem sub_rain (F : Factor A C) {B D : Finset A} (r : Rainbow F B) (db : D⊆B) :
    Rainbow F D := fun c => (inside_mono _ c db).trans (r c)

theorem color_classes (F : Factor A C) (B D : Finset A) (r : Rainbow F B) (db : D⊆B) (i : Fin 3) :
    (classColors F B D i).card = (rowData (Fintype.card C) Bᶜ.card B.card D.card i).colors := by
  classical
  by_cases zero : i=0
  · simpa [classColors,rowData,zero] using color_count F (sub_rain F r db)
  by_cases one : i=1
  · simpa [classColors,rowData,zero,one,card_sdiff db] using color_count F (sub_rain F r (sdiff_subset : B \ D ⊆ B))
  simp only [classColors,rowData,if_neg zero,if_neg one]
  have eq : (univ.filter (fun c => Inside F c B=0)) =
      (univ.filter (fun c => 0<Inside F c B))ᶜ := by ext; simp
  rw [eq,card_compl,color_count F r]

noncomputable def candidates (F : Factor A C) (c : C) (D U : Finset A) (s : Nat) : Finset (Finset A) := by
  classical
  exact (U.powersetCard s).filter (fun X => Closed (F.f c) (D ∪ X))

omit [Fintype A] [Fintype C] in
theorem candidate_mem {F : Factor A C} {c : C} {D U X : Finset A} {s : Nat} :
    X ∈ candidates F c D U s ↔ X ⊆ U ∧ X.card=s ∧ Closed (F.f c) (D ∪ X) := by
  classical
  simp [candidates,and_assoc]

private theorem realized_class (F : Factor A C) (c : C) (B D X : Finset A)
    (r : Rainbow F B) (db : D⊆B) (dis : Disjoint X B) (cl : Closed (F.f c) (D ∪ X)) :
    ∃ i : Fin 3, c ∈ classColors F B D i ∧
      (forced (F.f c) B D).card = (rowData (Fintype.card C) Bᶜ.card B.card D.card i).forced ∧
      (lowerEnds (F.f c) Bᶜ).card = (rowData (Fintype.card C) Bᶜ.card B.card D.card i).pairs := by
  have split := split_inside F c db dis cl
  have cap := r c
  have ex := external_size (F.invol c) (F.moving c) D
  rw [← forced_eq_external db dis cl] at ex
  have free := free_pair_size (F.invol c) (F.moving c) B
  change (forced _ _ _).card = D.card-2*Inside F c D at ex
  change 2*(lowerEnds _ _).card = Bᶜ.card-(B.card-2*Inside F c B) at free
  by_cases left : 0<Inside F c D
  · have l : Inside F c D=1 := by omega
    have b : Inside F c B=1 := by omega
    exact ⟨0,by simpa [classColors] using left,by simpa [rowData,l] using ex,by simp [rowData]; rw [b] at free; omega⟩
  by_cases right : 0<Inside F c (B \ D)
  · have l : Inside F c D=0 := by omega
    have b : Inside F c B=1 := by omega
    exact ⟨1,by simpa [classColors] using right,by simpa [rowData,l] using ex,by simp [rowData]; rw [b] at free; omega⟩
  · have l : Inside F c D=0 := by omega
    have b : Inside F c B=0 := by omega
    exact ⟨2,by simp [classColors,b],by simpa [rowData,l] using ex,by simp [rowData]; rw [b] at free; omega⟩

/-- Counts for one color in an arbitrary subfamily of its possible cuts.
If a marked point z is prescribed, either it is forced by a frozen point or
its ordinary matching edge must be selected. -/
theorem per_color (F : Factor A C) (c : C) (B D U : Finset A) (s : Nat) (S : Finset (Finset A))
    (r : Rainbow F B) (db : D⊆B) (ub : U⊆Bᶜ) (ne : S.Nonempty)
    (ok : S⊆candidates F c D U s) :
    ∃ i : Fin 3, c ∈ classColors F B D i ∧
      let row := rowData (Fintype.card C) Bᶜ.card B.card D.card i
      S.card ≤ rowAll row s U.card ∧ ∀ z, (∀ X ∈ S, z∈X) →
        (z ∈ forced (F.f c) B D → S.card ≤ rowSpecial row s U.card) ∧
        (z ∉ forced (F.f c) B D → F.f c z∈U ∧ S.card ≤ rowRegular row s U.card) := by
  classical
  obtain ⟨X0,h0⟩ := ne
  let f := F.f c
  let R := forced f B D
  have disX {X : Finset A} (xS : X∈S) : Disjoint X B :=
    disjoint_left.mpr (fun _ hx => mem_compl.mp (ub ((candidate_mem.mp (ok xS)).1 hx)))
  obtain ⟨i,hi,er,fr⟩ := realized_class F c B D X0 r db (disX h0) (candidate_mem.mp (ok h0)).2.2
  let row := rowData (Fintype.card C) Bᶜ.card B.card D.card i
  change R.card=row.forced at er
  change (lowerEnds f Bᶜ).card=row.pairs at fr
  have valid (X) (hx : X∈S) : X⊆U ∧ X.card=s ∧ R⊆X ∧ Closed f (X \ R) := by
    obtain ⟨sub,sz,cl⟩ := candidate_mem.mp (ok hx)
    exact ⟨sub,sz,strip_fixed (F.invol c) db (disX hx) cl⟩
  obtain ⟨xu,sz,rx,cl⟩ := valid X0 h0
  let k := (s-row.forced)/2
  let pool := min row.pairs ((U.card-row.forced)/2)
  have n := closed_size (F.invol c) (F.moving c) cl
  rw [card_sdiff rx,sz,er] at n
  change s-row.forced=2*(lowerEnds f (X0 \ R)).card at n
  have es : row.forced ≤ s := by rw [← er,← sz]; exact card_le_card rx
  have parity : (s-row.forced)%2=0 := by omega
  have cap : (lowerEnds f (U \ R)).card ≤ pool := by
    apply le_min
    · rw [← fr]
      exact card_le_card (lower_mono f (sdiff_subset.trans ub))
    · have b := ends_bound (F.invol c) (U \ R)
      rw [card_sdiff (rx.trans xu),er] at b
      change 2*(lowerEnds f (U \ R)).card ≤ U.card-row.forced at b
      omega
  have total : S.card ≤ rowAll row s U.card := by
    unfold rowAll
    rw [if_pos ⟨es,parity⟩,← Nat.choose_eq_fast_choose]
    have b := count_free (F.invol c) (F.moving c) U R S s valid
    rw [er] at b
    exact b.trans (Nat.choose_le_choose _ cap)
  refine ⟨i,hi,total,?_⟩
  intro z every
  constructor
  · intro zr
    have rp : row.forced≠0 := by rw [← er]; exact (card_pos.mpr ⟨z,zr⟩).ne'
    change S.card ≤ rowSpecial row s U.card
    simpa [rowSpecial,rp] using total
  · intro zr
    have hz : z ∈ X0 \ R := mem_sdiff.mpr ⟨every X0 h0,zr⟩
    have fp := cl z hz
    have kn : 0<k := by
      have pos := card_pos.mpr (show (X0 \ R).Nonempty from ⟨z,hz⟩)
      rw [card_sdiff rx,sz,er] at pos
      dsimp [k]
      omega
    have pp : 0<pool := by
      have sub := card_le_card (lower_mono f (sdiff_subset_sdiff xu (Subset.refl R)))
      have nc : 0<(lowerEnds f (X0 \ R)).card := by dsimp [k] at kn; omega
      exact nc.trans_le (sub.trans cap)
    refine ⟨xu (mem_sdiff.mp fp).1,?_⟩
    have b := count_through_pair (F.invol c) (F.moving c) U R S s z (fun X hx =>
      ⟨(valid X hx).1,(valid X hx).2.1,(valid X hx).2.2.1,(valid X hx).2.2.2,
       mem_sdiff.mpr ⟨every X hx,zr⟩⟩)
    rw [er] at b
    have bound := b.trans (Nat.choose_le_choose _ (Nat.sub_le_sub_right cap 1))
    change S.card ≤ rowRegular row s U.card
    change S.card ≤ if row.forced≤s ∧ (s-row.forced)%2=0 ∧ 0<k ∧ 0<pool then Nat.fast_choose (pool-1) (k-1) else 0
    rw [if_pos ⟨es,parity,kn,pp⟩,← Nat.choose_eq_fast_choose]
    exact bound
end WildSieve
