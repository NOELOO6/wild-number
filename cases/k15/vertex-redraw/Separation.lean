import Outside
namespace VertexRedraw
open EdgeWalk WildDeletion

def iterate (h : V → V) : Nat → V → V
  | 0,x => x
  | n+1,x => h (iterate h n x)
def period (a b : V→V) (n : Nat) (x : V) := iterate (fun v => a (b v)) n x=x
def signature (a b : V→V) :=
  (∀ x, period a b 8 x ∧ ¬period a b 4 x) ∨
  (∀ x, period a b 3 x ∨ period a b 5 x) ∨
  ((∀ x, period a b 2 x ∨ period a b 3 x) ∧ ¬∀ x, period a b 2 x)
instance (a b : V→V) : Decidable (signature a b) := by unfold signature period; infer_instance

def fromRows (rs : List (Array Nat)) (c : C) (v : V) : V := Fin.ofNat' 16 rs[c.val]![v.val]!
theorem references : ∀ c d : C, c≠d →
    signature (fromRows SearchExample.rows c) (fromRows SearchExample.rows d) ∧
    signature (fromRows roundRobin c) (fromRows roundRobin d) := by native_decide
theorem six_limit : ∀ s : Fin 32768, clique s.val=true → size s.val≤6 := by native_decide
theorem pair_comparison : ∀ c d : C, d.val<c.val →
    signature (partner c) (partner d) → pairMasks[c.val]!.testBit d.val=true := by native_decide
/-- No three ordinary points of this example, with the root, are paired
internally by three colors. It also falls outside the three-star test. -/
theorem no_starting_triple : ((List.range 32768).all fun s => size s != 3 ||
    (colors.filter (fun c => points.all fun x =>
      !(s ||| 32768).testBit x.val || (s ||| 32768).testBit (partner c x).val)).length < 3)=true := by native_decide

private theorem agrees {a b u v : V→V} (p : V→V) (inj : ∀ x y, p x=p y → x=y)
    (ha : ∀ x, p (a x)=u (p x)) (hb : ∀ x, p (b x)=v (p x)) (n : Nat) (x : V) :
    period a b n x ↔ period u v n (p x) := by
  have eq : p (iterate (fun y => a (b y)) n x)=iterate (fun y => u (v y)) n (p x) := by
    induction n with
    | zero => rfl
    | succ k ih => simp only [iterate,ha,hb,ih]
  exact ⟨fun h => eq.symm.trans (congrArg p h),fun h => inj _ _ (eq.trans h)⟩

/-- Renaming points and colors preserves the tests based on alternating steps. -/
theorem pull_signature {a b u v : V→V} (p : V→V) (inj : ∀ x y, p x=p y → x=y)
    (onto : ∀ y, ∃ x, p x=y) (ha : ∀ x, p (a x)=u (p x)) (hb : ∀ x, p (b x)=v (p x))
    (h : signature u v) : signature a b := by
  let eq := agrees p inj ha hb
  rcases h with high|middle|⟨low,nontrivial⟩
  · exact Or.inl fun x => ⟨(eq 8 x).mpr (high _).1,fun z => (high _).2 ((eq 4 x).mp z)⟩
  · exact Or.inr (Or.inl fun x => (middle (p x)).imp (eq 3 x).mpr (eq 5 x).mpr)
  · refine Or.inr (Or.inr ⟨fun x => (low (p x)).imp (eq 2 x).mpr (eq 3 x).mpr,fun all => nontrivial ?_⟩)
    intro y
    obtain ⟨x,rfl⟩ := onto y
    exact (eq 2 x).mp (all x)

private theorem small_and {s : Nat} (c : C) (h : ∀ d : C, d.val<c.val → s.testBit d.val=true →
    pairMasks[c.val]!.testBit d.val=true) :
    (s &&& (2^c.val-1) &&& pairMasks[c.val]!)=(s &&& (2^c.val-1)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases small : j<c.val
  · have bound : j<15 := Nat.lt_trans small c.isLt
    cases b : s.testBit j with
    | false => simp [Nat.testBit_and,b]
    | true =>
      have yes := h ⟨j,bound⟩ small b
      simp [Nat.testBit_and,b,show pairMasks[c.val]!.testBit j=true from yes]
  · simp [Nat.testBit_and,Nat.testBit_two_pow_sub_one,small]

/-- The concrete coloring shares at most six complete matching rows with
either six-color redraw template, after arbitrary point and color renaming. -/
theorem at_most_six (s : Fin 32768) (base : C→V→V)
    (which : base=fromRows SearchExample.rows ∨ base=fromRows roundRobin)
    (p : V→V) (pinj : ∀ x y, p x=p y → x=y) (onto : ∀ y, ∃ x, p x=y)
    (name : C→C) (cinj : ∀ x y,name x=name y → x=y)
    (keep : ∀ c, s.val.testBit c.val=true → ∀ x,p (partner c x)=base (name c) (p x)) :
    size s.val≤6 := by
  apply six_limit s
  apply Array.all_eq_true.mpr
  intro n mem
  have bound : n<15 := by simpa using mem
  let c : C := ⟨n,bound⟩
  cases yes : s.val.testBit n with
  | false => simp [yes]
  | true =>
    have eq := small_and (s:=s.val) c (fun d less hd => by
      have diff : name c≠name d := fun same => (Nat.ne_of_lt less) (congrArg Fin.val (cinj _ _ same)).symm
      have test : signature (base (name c)) (base (name d)) := by
        rcases which with rfl|rfl
        · exact (references _ _ diff).1
        · exact (references _ _ diff).2
      exact pair_comparison _ _ less (pull_signature p pinj onto (keep c yes) (keep d hd) test))
    simp [yes,show s.val &&& (2^n-1) &&& pairMasks[n]! = s.val &&& (2^n-1) from eq]
    simpa [c] using eq
#print axioms at_most_six
end VertexRedraw
