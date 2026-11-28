import PairPlacement
import StarDraw
import UniversalLower
namespace WildAnchor
open Finset WildExact WildDeletion WildSieve
variable {m n k t : Nat}
abbrev Index (m : Nat) := Fin m
abbrev Point (m : Nat) := Pts (Fin m)

def row {m : Nat} (next : Equiv.Perm (Fin m)) (mask : Fin m → Bool) : State (Fin m) :=
  fun i => (mask i,mask (next.symm i))

/-- Each other matching is given in its own numbering and orientation of the
same anchor edges. The cycles of next describe its union with the anchor. -/
def InFrame (g : Coloring n k) (a : Fin k) (e : Point m ≃ Fin n)
    (next : {c : Fin k // c≠a} → Equiv.Perm (Fin m)) : Prop :=
  (∀ i,g.paint (e (i,false)) (e (i,true))=a) ∧
  ∀ c,∃ q : Shuffle (Fin m),∀ i,
    g.paint (e (perm q (i,false))) (e (perm q (next c i,true)))=c.val

def region (tag : Point m → Fin t) (j : Fin t) := univ.filter fun x => tag x=j
def starCost (tag : Point m → Fin t) := ∑ j,((region tag j).card-1)

/-- A winning shuffle gives legal ordinary wild edges. A disconnected color
would supply a whole union of template groups and a closed matching side
with exactly the same image. -/
theorem anchored_upper_of_selection {A B : Type} [Fintype A] [Fintype B]
    (g : Coloring n k) (a : Fin k) (e : Point m ≃ Fin n)
    (next : {c : Fin k // c≠a} → Equiv.Perm (Fin m)) (frame : InFrame g a e next)
    (tag : Point m → Fin t) (root : Point m)
    (s : A → State (Fin m)) (masks : B → Fin m → Bool)
    (allMasks : ∀ f : Fin m → Bool,∃ b,masks b=f)
    (allSides : ∀ h : Fin t → Bool,h (tag root)=false → (∃ j,h j=true) →
      ∃ i,s i=state (fun x => h (tag x)))
    (anchorPass : ∀ i,∃ j,(s i j).1≠(s i j).2)
    (select : ∀ coords : {c : Fin k // c≠a} → Shuffle (Fin m), ∃ p : Shuffle (Fin m),
      ∀ c i b, ¬Fits p (s i) (transport (coords c) (row (next c) (masks b)))) :
    Upper g (starCost tag) := by
  classical
  choose q hq using frame.2
  obtain ⟨p,safe⟩ := select q
  let label := (perm p).trans e
  let group (j) := (region tag j).map label.toEmbedding
  let w := univ.biUnion fun j => spokes (group j)
  refine ⟨w,fun edge he => ?_,?_,?_⟩
  · obtain ⟨j,_,h⟩ := mem_biUnion.mp he
    exact spokes_legal _ _ h
  · apply card_biUnion_le.trans
    apply sum_le_sum
    intro j _
    exact (spokes_bound _).trans (by rw [show (group j).card=(region tag j).card from card_map _])
  intro c
  let E := Joined g w c
  let reach (v) := Walk E (label root) v
  have colored {x y} (ne : x≠y) (col : g.paint x y=c) : reach x ↔ reach y :=
    ⟨fun h => .step h (Or.inr ⟨ne,col⟩),fun h => .step h (Or.inr ⟨ne.symm,(g.symm y x).trans col⟩)⟩
  have inside {x y : Point m} (same : tag x=tag y) : reach (label x) ↔ reach (label y) := by
    have route {u v : Point m} (h : tag u=tag v) : Walk E (label u) (label v) := by
      apply Walk.mapInto (E:=Touch w) id (fun _ _ hit => .step (.stay _) (Or.inl hit))
      apply in_star (w:=w) (T:=group (tag v)) (fun edge he => mem_biUnion.mpr ⟨_,mem_univ _,he⟩)
      · exact mem_map.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
      · exact mem_map.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩
    exact ⟨fun h => h.join (route same),fun h => h.join (route same.symm)⟩
  have all (v : Fin n) : reach v := by
    apply Classical.byContradiction
    intro no
    let h (j : Fin t) := decide (∃ u : Point m, tag u=j ∧ ¬reach (label u))
    have hk (x) : h (tag x)=decide (¬reach (label x)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [h,decide_eq_true_eq]
      exact ⟨fun ⟨y,eq,out⟩ => fun hx => out ((inside eq).mpr hx),fun hx => ⟨x,rfl,hx⟩⟩
    have base : h (tag root)=false := by
      rw [hk]; simp [reach,show Walk E (label root) (label root) from .stay _]
    have non : h (tag (label.symm v))=true := by rw [hk];simpa using no
    obtain ⟨i,si⟩ := allSides h base ⟨_,non⟩
    let observed := state (fun z : Point m => decide (¬reach (e z)))
    have fits : Fits p (s i) observed := by
      apply (fits_iff ..).mpr
      intro x
      simpa only [si,observed,flag_state] using hk x
    by_cases ca : c=a
    · obtain ⟨j,jj⟩ := anchorPass i
      have paired (l : Fin m) : (observed l).1=(observed l).2 := by
        apply Bool.eq_iff_iff.mpr
        simp only [observed,state,decide_eq_true_eq,not_iff_not]
        apply colored (e.injective.ne (by simp))
        exact (frame.1 l).trans ca.symm
      have same := paired (p.1 j)
      rw [←fits j] at same
      cases bit : p.2 j <;> simp [flip,bit] at same
      · exact jj same
      · exact jj same.symm
    · let d : {z : Fin k // z≠a} := ⟨c,ca⟩
      let f (j : Fin m) := decide (¬reach (e (perm (q d) (j,false))))
      obtain ⟨b,hb⟩ := allMasks f
      have pointwise (v : Point m) : flag observed v=flag (transport (q d) (row (next d) (masks b))) v := by
        obtain ⟨⟨l,bit⟩,rfl⟩ := (perm (q d)).surjective v
        simp only [observed,transport,flag_state,Equiv.symm_apply_apply,hb]
        cases bit
        · rfl
        · change decide (¬reach (e (perm (q d) (l,true))))=
              decide (¬reach (e (perm (q d) ((next d).symm l,false))))
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq,not_iff_not]
          apply Iff.symm
          apply colored ((e.injective.comp (perm (q d)).injective).ne (by simp))
          simpa only [Equiv.apply_symm_apply] using hq d ((next d).symm l)
      have same : observed=transport (q d) (row (next d) (masks b)) :=
        funext (fun j => Prod.ext (pointwise (j,false)) (pointwise (j,true)))
      exact safe d i b (same ▸ fits)
  exact fun x y => (backwards (joined_symm g) (all x)).join (all y)

/-- A winning shuffle gives legal ordinary wild edges. A disconnected color
would supply a whole union of template groups and a closed matching side
with exactly the same image. -/
theorem anchored_upper {A B : Type} [Fintype A] [Fintype B]
    (g : Coloring n k) (a : Fin k) (e : Point m ≃ Fin n)
    (next : {c : Fin k // c≠a} → Equiv.Perm (Fin m)) (frame : InFrame g a e next)
    (tag : Point m → Fin t) (root : Point m)
    (s : A → State (Fin m)) (masks : B → Fin m → Bool)
    (allMasks : ∀ f : Fin m → Bool,∃ b,masks b=f)
    (allSides : ∀ h : Fin t → Bool,h (tag root)=false → (∃ j,h j=true) →
      ∃ i,s i=state (fun x => h (tag x)))
    (anchorPass : ∀ i,∃ j,(s i j).1≠(s i j).2)
    (budget : (∑ c,∑ i,∑ b,price (s i) (row (next c) (masks b))) < m.factorial*2^m) :
    Upper g (starCost tag) :=
  anchored_upper_of_selection g a e next frame tag root s masks allMasks allSides anchorPass
    fun q => choose_shuffle s (fun c b => row (next c) (masks b)) q (by simpa using budget)

end WildAnchor
