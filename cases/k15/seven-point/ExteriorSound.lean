import ExteriorChecks
namespace ExteriorRows
open VertexRedraw EdgeWalk ThreeStars WildDeletion
set_option maxRecDepth 5000

private theorem inShadow {i : Nat} (ss : List Nat) (initial : Nat) (s : Nat) (mem : s∈ss)
    (yes : (bySide[s]?.getD 0).testBit i=true) :
    (ss.foldl (fun n a => n ||| bySide[a]?.getD 0) initial).testBit i=true := by
  have keep (ls : List Nat) (n : Nat) (h : n.testBit i=true) :
      (ls.foldl (fun a k => a ||| bySide[k]?.getD 0) n).testBit i=true := by
    induction ls generalizing n with
    | nil => exact h
    | cons a ls ih => exact ih _ (by simp [Nat.testBit_or,h])
  induction ss generalizing initial with
  | nil => simp at mem
  | cons a ss ih =>
    rcases List.mem_cons.mp mem with rfl|inTail
    · exact keep ss _ (by rw [Nat.testBit_or,yes,Bool.or_true])
    · exact ih _ inTail

private theorem clear {m : R} (j : Fin 280) (i : Fin 10)
    (h : (shadow m).testBit (index j i)=false) : spoils (layout j i) m=false := by
  cases eq : spoils (layout j i) m with
  | false => rfl
  | true =>
    obtain ⟨s,mem,side⟩ := List.any_eq_true.mp eq
    have yes := List.all_eq_true.mp (sideTable j i) s (by simpa using side)
    have flag : (shadow m).testBit (index j i)=true := inShadow _ 0 _ mem yes
    rw [h] at flag
    exact False.elim (Bool.false_ne_true flag)

private theorem count_eq (s : Nat) (j : Fin 280) :
    count s j=Teams.total groups (fun i => if s.testBit (index j i) then 1 else 0) := by
  have lut : (List.range 1024).all (fun k => bits10[k]! == Teams.total groups
      (fun i => if k.testBit i.val then 1 else 0)) = true := by native_decide
  have bounds : digit s j < 1024 := Nat.mod_lt _ (by decide)
  have val := beq_iff_eq.mp (List.all_eq_true.mp lut (digit s j) (List.mem_range.mpr bounds))
  have b (i : Fin 10) : (digit s j).testBit i.val = s.testBit (index j i) := by
    simp only [digit,show (1024:Nat)=2^10 by decide,Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight,index,decide_eq_true i.isLt,Bool.true_and]
  change bits10[digit s j]! = _
  simpa only [b] using val

/-- Count the actual disconnected color graphs for one of the ten starts. -/
noncomputable def failures (f : C→V→V) (j : Fin 280) (i : Fin 10) : Nat := by
  classical
  exact Teams.total colors (fun c => if Connected (Adj (wild (layout j i) ++ actualEdges (f c))) then 0 else 1)

/-- Multiple colors can fail on the same grouping. Each failure beyond the
first gives back one unit of the budget for this exterior ending. -/
theorem overlap_winner (f : C→V→V) (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (agree : ∀ c x, BoundaryOptions.fixedAt lock c x=true → f c x=SixBoundary.ref c x)
    (j : Fin 280) (cheap : budget (fun c => key (f c 15)) j <
      10 + Teams.total groups (fun i => failures f j i - 1)) :
    ∃ g ∈ FixedSix.all, (trial g).length=10 ∧ (trial g).Nodup ∧
      ∀ c, Connected (Adj (trial g++actualEdges (f c))) := by
  classical
  have select (c) := BoundaryOptions.represented lock (by native_decide) f inv ne proper agree c
  let row (c : C) := Classical.choose (select c)
  have spec (c) : row c∈BoundaryOptions.possible lock c ∧ respects (f c) (row c) :=
    Classical.choose_spec (select c)
  have verified (c) : assessed c (row c)=true := by
    have h := List.all_eq_true.mp every_row c ((by decide : ∀ d : C,d∈colors) _)
    apply Array.all_eq_true_iff_forall_mem.mp h
    have hm := (spec c).1
    rw [←options_table] at hm
    simpa using hm
  have mate (c) : root (row c)=f c 15 := by
    have flag := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (verified c)).1).2
    rcases Bool.or_eq_true_iff.mp flag with left|right
    · have eq := (spec c).2 _ (List.contains_iff_mem.mp left)
      exact ((congrArg (f c) eq).symm.trans (inv c _)).symm
    · exact ((spec c).2 _ (List.contains_iff_mem.mp right)).symm
  let fail (i : Fin 10) (c : C) := if (shadow (row c)).testBit (index j i) then 1 else 0
  have budgeted (c) : Teams.total groups (fun i => fail i c) ≤ price c (key (f c 15)) j.val := by
    have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (verified c)).2 j
      ((by decide : ∀ j : Fin 280, j∈ends) _)
    simpa [count_eq,mate,fail] using h
  have total : Teams.total groups (fun i => Teams.total colors (fail i)) ≤ budget (fun c => key (f c 15)) j := by
    rw [Teams.transpose]
    exact Teams.total_mono _ _ _ (fun c _ => budgeted c)
  have path (c i) (off : (shadow (row c)).testBit (index j i)=false) :
      Connected (Adj (wild (layout j i)++actualEdges (f c))) := by
    have complete := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (verified c)).1).1
    exact path_of_unblocked _ (shapes j i).1 _ (by simpa using complete) _ (inv c) (ne c) (spec c).2 (clear _ _ off)
  have actual (i : Fin 10) : failures f j i ≤ Teams.total colors (fail i) := by
    unfold failures
    apply Teams.total_mono
    intro c _
    cases e : (shadow (row c)).testBit (index j i) with
    | false => simp [path c i e,fail,e]
    | true => split <;> simp [fail,e]
  have existsZero : ∃ i ∈ groups, Teams.total colors (fail i)=0 := by
    apply Classical.byContradiction
    intro no
    have point (i) (mem : i∈groups) : 1+(failures f j i-1)≤Teams.total colors (fail i) := by
      have pos : Teams.total colors (fail i)≠0 := fun e => no ⟨i,mem,e⟩
      have le := actual i
      omega
    have bound := Teams.total_mono groups (fun i => (1:Nat)+(failures f j i-1)) _ point
    rw [Teams.total_add groups (fun _ => 1) (fun i => failures f j i-1),
        show Teams.total groups (fun _ => 1)=10 by decide] at bound
    omega
  obtain ⟨i,_,none⟩ := existsZero
  have geom := shapes j i
  refine ⟨(layout j i).groups,geom.2.1,geom.2.2.1,geom.2.2.2,?_⟩
  intro c
  have single {α : Type} (xs : List α) (p : α→Nat) (x : α) (h : x∈xs) :
      p x ≤ Teams.total xs p := by
    induction xs with
    | nil => simp at h
    | cons y ys ih =>
      rw [Teams.total_cons]
      rcases List.mem_cons.mp h with rfl|t
      · omega
      · have := ih t; omega
  have only := single colors (fail i) c ((by decide : ∀ d : C,d∈colors) _)
  rw [none] at only
  have off : (shadow (row c)).testBit (index j i)=false := by
    cases e : (shadow (row c)).testBit (index j i) <;> simp_all [fail]
  exact path c i off

/-- If the total number of starts that the fifteen colors can spoil is
less than ten for some exterior ending, one of its ten starts connects
every color. The 36 exterior lines are the only ordinary edges prescribed. -/
theorem price_winner (f : C→V→V) (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (agree : ∀ c x, BoundaryOptions.fixedAt lock c x=true → f c x=SixBoundary.ref c x)
    (j : Fin 280) (cheap : budget (fun c => key (f c 15)) j < 10) :
    ∃ g ∈ FixedSix.all, (trial g).length=10 ∧ (trial g).Nodup ∧
      ∀ c, Connected (Adj (trial g++actualEdges (f c))) :=
  overlap_winner f inv ne proper agree j (by omega)
#print axioms overlap_winner
#print axioms price_winner
end ExteriorRows
