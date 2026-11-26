import OutsideNames
import ExteriorEligibility
import ExteriorSound
namespace SevenOutside
open VertexRedraw EdgeWalk WildDeletion ExteriorRows InsideNames
open SixBoundary (ref)

def named (a b : C) (x : V) := if x=10 then a else if x=14 then b else missing x
def codes (a b : C) := nine.map (named a b)
def kind (a b c : C) := ((codes a b).idxOf? c).map (·+1) |>.getD 0
def legal (a b : C) := decide (codes a b).Nodup &&
  required.all ((codes a b).contains ·) &&
  nine.all (fun x => (pricesAt x).contains (named a b x))
theorem priced : ∀ a b : C, legal a b=true →
    (a=9 ∧ b=12) ∨ budget (kind a b) 106<10 := by native_decide

/-- All 69 incident edges and the missing colors at the chosen six and at
outside points 10 and 14 may vary together. -/
theorem two_outside_free (known : OutsideFixed) (f : C→V→V)
    (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d,c≠d → ∀ x,f c x≠f d x) (cover : ∀ x y : V,x≠y → ∃ c,f c x=y)
    (agree : ∀ c x, BoundaryOptions.fixedAt ExteriorRows.lock c x=true → f c x=ref c x)
    (seven : ∀ x ∈ nine, x≠10 → x≠14 → f (missing x) 15=x) : RedrawModel.Wins f := by
  classical
  obtain ⟨a,ha⟩ := cover 15 10 (by decide)
  obtain ⟨b,hb⟩ := cover 15 14 (by decide)
  have namedAt (x) (hx : x∈nine) : f (named a b x) 15=x := by
    by_cases h : x=10
    · subst x; simpa [named] using ha
    by_cases t : x=14
    · subst x; simpa [named] using hb
    · simpa [named,h,t] using seven x hx h t
  have fits (c) : (oldCount c ≠ 1 ∨ outside (f c 15)=true) ∧
      (outside (f c 15)=true → c∈pricesAt (f c 15)) := by
    obtain ⟨m,mem,res⟩ := BoundaryOptions.represented ExteriorRows.lock (by native_decide) f inv ne proper agree c
    have am : m∈opts[c.val]! := by
      rw [←options_table] at mem; simpa using mem
    have cm := (by decide : ∀ c : C,c∈colors) c
    have checks := Array.all_eq_true_iff_forall_mem.mp (List.all_eq_true.mp eligibility_checked.2 c cm) m am
    have assessed := Array.all_eq_true_iff_forall_mem.mp (List.all_eq_true.mp every_row c cm) m am
    have rootEq : root m=f c 15 := by
      rcases Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp assessed).1).2 with l|r
      · exact ((congrArg (f c) (res _ (List.contains_iff_mem.mp l))).symm.trans (inv c _)).symm
      · exact (res _ (List.contains_iff_mem.mp r)).symm
    have first := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checks).1).2
    have second := (Bool.and_eq_true_iff.mp checks).2
    rw [rootEq] at first second
    exact ⟨by simpa using first,fun h => by simpa [h] using second⟩
  have inNine (x : V) : x∈nine ↔ outside x=true :=
    (by decide : ∀ x : V, x∈nine ↔ outside x=true) x
  have idEq (c x) (hx : x∈nine) : named a b x=c ↔ f c 15=x := by
    constructor
    · intro h; rw [←h]; exact namedAt x hx
    · intro h; apply Classical.byContradiction; intro diff
      exact proper _ _ diff 15 ((namedAt x hx).trans h.symm)
  have valid : legal a b=true := by
    have distinct : (codes a b).Nodup := by
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem _ (by decide : nine.Nodup)
      intro x y hx hy diff eq
      exact diff ((namedAt x hx).symm.trans ((congrArg (fun c => f c 15) eq).trans (namedAt y hy)))
    have req : required.all ((codes a b).contains ·)=true := by
      apply List.all_eq_true.mpr
      intro c hc
      have n : oldCount c=1 := by simpa [required] using (List.mem_filter.mp hc).2
      have mem := (inNine _).2 ((fits c).1.resolve_left (not_not_intro n))
      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨_,mem,(idEq c _ mem).2 rfl⟩)
    have outsideGood : nine.all (fun x => (pricesAt x).contains (named a b x))=true := by
      apply List.all_eq_true.mpr
      intro x hx
      have h := (fits (named a b x)).2
      rw [namedAt x hx] at h
      exact List.contains_iff_mem.mpr (h ((inNine x).1 hx))
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true distinct,req⟩,outsideGood⟩
  rcases priced a b valid with ⟨rfl,rfl⟩|cheap
  · apply known f inv ne proper cover
    intro c x hx hy
    have star (y) (h : y∈nine) : f (missing y) 15=y := by
      have id : ∀ z : V,named 9 12 z=missing z := by native_decide
      simpa only [id] using namedAt y h
    have ri : ∀ c x,ref c (ref c x)=x := by native_decide
    have old (c) (high : 6≤(ref c 15).val) : f c 15=ref c 15 := by
      have m := (by native_decide : ∀ c : C, 6≤(ref c 15).val → ref c 15∈nine) c high
      simpa only [(by native_decide : ∀ c : C, missing (ref c 15)=c) c] using star _ m
    by_cases rootX : x=15
    · subst x; exact old c hy
    by_cases rootY : ref c x=15
    · have eq : ref c 15=x := by rw [←rootY,ri]
      have both := old c (by simpa [eq] using hx)
      rw [eq] at both
      exact ((congrArg (f c) both).symm.trans (inv c 15)).trans rootY.symm
    · apply agree
      have xl : x.val<15 := by have := x.isLt; have : x.val≠15 := fun e => rootX (Fin.ext e); omega
      have yl : (ref c x).val<15 := by have := (ref c x).isLt; have : (ref c x).val≠15 := fun e => rootY (Fin.ext e); omega
      simp [BoundaryOptions.fixedAt,ExteriorRows.lock,outside,hx,hy,xl,yl]
  · apply price_winner f inv ne proper agree 106
    have ident : ∀ (a b c : C) (x : V), nine.all (fun y => (named a b y==c)==(x==y))=true →
        key x=kind a b c := by native_decide
    have kindEq (c) : key (f c 15)=kind a b c := by
      apply ident
      apply List.all_eq_true.mpr
      intro y hy
      apply beq_iff_eq.mpr
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using idEq c y hy
    simpa only [kindEq] using cheap
#print axioms two_outside_free
end SevenOutside
