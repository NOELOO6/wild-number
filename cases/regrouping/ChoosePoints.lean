import DetourCount
namespace WildExact.Regroup.Switch
open Finset WildDeletion
variable {V I : Type} [LinearOrder V] [Fintype I]

omit [LinearOrder V] in
private theorem stays {W : V → V → Prop} {m : V → V} (S : Finset V)
    (parts : ∀ a b, Walk (WithMatching W m) a b ↔ (a∈S ↔ b∈S)) (v : V) : v∈S ↔ m v∈S :=
  (parts v (m v)).mp (.step (.stay _) (Or.inr (Or.inr rfl)))

private def restrictPartner (S : Finset V) (m : V → V) (cl : ∀ v,v∈S ↔ m v∈S) (x : S) : S :=
  ⟨m x.val,(cl _).mp x.property⟩

omit [LinearOrder V] in
private theorem interior {W : V → V → Prop} {m : V → V} (S : Finset V)
    (parts : ∀ a b, Walk (WithMatching W m) a b ↔ (a∈S ↔ b∈S)) :
    Connected (WithMatching (fun a b : S => W a.val b.val) (restrictPartner S m (stays S parts))) := by
  intro a b
  have lift {v : V} (h : Walk (WithMatching W m) a.val v) (hv : v∈S) :
      Walk (WithMatching (fun a b : S => W a.val b.val) (restrictPartner S m (stays S parts))) a ⟨v,hv⟩ := by
    induction h with
    | stay => exact .stay _
    | @step u z p e ih =>
      have hu := ((parts _ _).mp p).mp a.property
      apply Walk.step (ih hu)
      rcases e with eq|w|mz
      · exact Or.inl (Subtype.ext eq)
      · exact Or.inr (Or.inl w)
      · exact Or.inr (Or.inr (Subtype.ext mz))
  exact lift ((parts _ _).mpr ⟨fun _ => b.property,fun _ => a.property⟩) b.property

/-- In a component S of a two-piece color, each selected matching edge
allows either endpoint to exchange with *every* point in the other piece.
The number of selected edges is at least |S|/2 minus the number of groups
in S plus one. -/
theorem choose_across (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a)
    (m : V → V) (inv : Function.Involutive m) (free : ∀ a,a≠m a)
    (S : Finset V) (pos : S.Nonempty)
    (parts : ∀ a b, Walk (WithMatching W m) a b ↔ (a∈S ↔ b∈S))
    (tag : S → I) (group : ∀ a b : S, tag a=tag b → Walk (fun u v : S => W u.val v.val) a b) :
    ∃ U : Finset S,S.card+2≤2*U.card+2*Fintype.card I ∧
      ∀ x∈U,x.val<m x.val ∧ ∀ z : V,z=x.val ∨ z=m x.val → ∀ y,y∉S →
        Connected (WithMatching (regrouped W z y) m) := by
  classical
  letI : Nonempty S := ⟨⟨pos.choose,pos.choose_spec⟩⟩
  let W₀ (a b : S) := W a.val b.val
  let m₀ := restrictPartner S m (stays S parts)
  have inverse : Function.Involutive m₀ := fun v => Subtype.ext (inv v.val)
  have moving : ∀ v,v≠m₀ v := fun v eq => free v.val (congrArg Subtype.val eq)
  obtain ⟨U,num,paths⟩ := many_detours tag W₀ (fun e => sym e) group m₀ inverse moving (interior S parts)
  refine ⟨U,by simpa only [Fintype.card_coe] using num,?_⟩
  intro x hx
  obtain ⟨xm,route⟩ := paths x hx
  refine ⟨xm,?_⟩
  intro z endpoint y outside
  have zs : z∈S := endpoint.elim (fun e => e ▸ x.property) (fun e => e ▸ (stays S parts _).mp x.property)
  have my : m y∉S := fun h => outside ((stays S parts _).mpr h)
  apply (repair_two_components W sym m inv free z y ?_ ?_).mpr
  · apply Or.inl
    have middle : Walk (Remainder W m z y) x.val (m x.val) := by
      apply route.mapInto Subtype.val
      rintro a b (w|⟨nx,nm,eq⟩)
      · exact .step (.stay _) (Or.inr (Or.inl w))
      · have az : a.val≠z ∧ a.val≠m z := by
          rcases endpoint with e|e
          · rw [e];exact ⟨fun h => nx (Subtype.ext h),fun h => nm (Subtype.ext h)⟩
          · rw [e,inv];exact ⟨fun h => nm (Subtype.ext h),fun h => nx (Subtype.ext h)⟩
        refine .step (.stay _) (Or.inr (Or.inr ⟨?_,congrArg Subtype.val eq⟩))
        intro i
        have cases4 : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
        rcases cases4 i with rfl|rfl|rfl|rfl
        · exact az.1
        · exact az.2
        · change a.val≠y
          exact fun h => outside (h ▸ a.property)
        · change a.val≠m y
          exact fun h => my (h ▸ a.property)
    rcases endpoint with e|e
    · exact e ▸ middle
    · have reverse := backwards (remainder_sym W sym m inv z y) middle
      simpa only [e,inv x.val] using reverse
  · intro v
    by_cases hit : v∈S
    · exact Or.inl ((parts _ _).mpr ⟨fun _ => zs,fun _ => hit⟩)
    · exact Or.inr ((parts _ _).mpr ⟨fun h => (hit h).elim,fun h => (outside h).elim⟩)
  · exact fun path => outside (((parts _ _).mp path).mp zs)

#print axioms choose_across
end WildExact.Regroup.Switch
