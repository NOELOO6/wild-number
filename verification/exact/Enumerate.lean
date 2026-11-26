import MatchingModel
namespace WildExact
open WildDeletion Finset
abbrev Row (n : Nat) := List (Fin (n+1) × Fin (n+1))

def enumerate {n} : Nat → List (Fin (n+1)) → List (Row n)
  | _, [] => [[]]
  | 0, _::_ => []
  | fuel+1, x::xs => xs.flatMap fun y =>
      (enumerate fuel (xs.filter (· != y))).map ((x,y)::·)

def Rows (n : Nat) := enumerate (n+1) (List.finRange (n+1))

def Respects {n} (f : Fin (n+1) → Fin (n+1)) (m : Row n) := ∀ e ∈ m, f e.1 = e.2

theorem enumerate_complete {n} (f : Fin (n+1) → Fin (n+1))
    (inv : Function.Involutive f) (ne : ∀ x, x ≠ f x)
    (fuel) (xs : List (Fin (n+1))) (len : xs.length ≤ fuel)
    (unique : xs.Nodup) (stable : ∀ x ∈ xs, f x ∈ xs) : ∃ m ∈ enumerate fuel xs, Respects f m := by
  induction fuel generalizing xs with
  | zero => have := List.length_eq_zero_iff.mp (by omega : xs.length=0); subst xs; exact ⟨[],by simp [enumerate],by simp [Respects]⟩
  | succ fuel ih =>
    cases xs with
    | nil => exact ⟨[],by simp [enumerate],by simp [Respects]⟩
    | cons x xs =>
      let y := f x
      have hy : y∈xs := (List.mem_cons.mp (stable x (by simp))).resolve_left (ne x).symm
      let rest := xs.filter (· != y)
      have hr : rest.length ≤ fuel := (List.length_filter_le ..).trans (by simpa using len)
      have st : ∀ z ∈ rest, f z ∈ rest := by
        intro z hz
        obtain ⟨mem,other⟩ := List.mem_filter.mp hz
        have nz : z≠y := by simpa using other
        by_cases zx : z=x
        · subst z
          -- A list of remaining points contains no second copy of x.
          exact False.elim ((List.nodup_cons.mp unique).1 mem)
        have n1 : f z≠x := fun eq => nz ((inv z).symm.trans (congrArg f eq))
        have n2 : f z≠y := fun eq => zx (inv.injective eq)
        exact List.mem_filter.mpr ⟨(List.mem_cons.mp (stable z (by simp [mem]))).resolve_left n1,by simpa using n2⟩
      obtain ⟨m,hm,res⟩ := ih rest hr ((List.nodup_cons.mp unique).2.filter _) st
      refine ⟨(x,y)::m,List.mem_flatMap.mpr ⟨y,hy,List.mem_map.mpr ⟨m,hm,rfl⟩⟩,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl|h
      · rfl
      · exact res e h

theorem choose_rows {n} (g : Coloring (n+1) n) :
    ∃ rs : Fin n → Row n, ∀ c, rs c ∈ Rows n ∧ Respects (mate g c) (rs c) := by
  classical
  have ex (c : Fin n) : ∃ m ∈ Rows n, Respects (mate g c) m := by
    apply enumerate_complete (mate g c) (mate_involutive g c) (fun x => (mate_spec g c x).1)
    · simp
    · exact List.nodup_finRange _
    · exact fun _ _ => List.mem_finRange _
  choose rs mem res using ex
  exact ⟨rs,fun c => ⟨mem c,res c⟩⟩

/-- Delete the temporary point, retaining actual ordinary edges. -/
def eraseRoot {n} (m : Row n) : List (EdgeWalk.Edge n) := m.filterMap fun e =>
  if h : e.1.val<n ∧ e.2.val<n then some (⟨e.1,h.1⟩,⟨e.2,h.2⟩) else none

abbrev TestLines (n : Nat) := List (EdgeWalk.Edge n)
def passesRow {n} (r : Fin n) (w : TestLines n) (m : Row n) :=
  EdgeWalk.passes r (w ++ eraseRoot m)

theorem from_rows {n} (hn : n%2=1) (g : Coloring n n) (rs : Fin n → Row n)
    (owned : ∀ c, Respects (mate (augment hn g) c) (rs c))
    (root : Fin n) (w : TestLines n) (b : Nat)
    (size : w.length ≤ b) (order : ∀ e∈w, e.1<e.2)
    (ok : ∀ c, passesRow root w (rs c)=true) : Upper g b := by
  refine ⟨w.toFinset,fun e he => order e (List.mem_toFinset.mp he),(List.toFinset_card_le w).trans size,?_⟩
  intro c a z
  have lift {x y} (h : (x,y)∈ w ++ eraseRoot (rs c)) : Joined g w.toFinset c x y := by
    rcases List.mem_append.mp h with hw|hm
    · exact Or.inl (Or.inl (List.mem_toFinset.mpr hw))
    obtain ⟨⟨u,v⟩,mem,image⟩ := List.mem_filterMap.mp hm
    dsimp at image
    split at image
    next bound =>
      cases image
      obtain ⟨ne,eq⟩ := mate_spec (augment hn g) c u
      rw [owned c (u,v) mem] at ne eq
      refine Or.inr ⟨fun h => ne (Fin.ext (congrArg (fun i : Fin n => i.val) h)),?_⟩
      rw [←augment_paint hn]
      exact eq
    next => contradiction
  have wlk := EdgeWalk.connected_of_passes root _ (ok c) a z
  exact Walk.mapInto id (fun _ _ h => Walk.step (.stay _) (h.elim lift (fun e => joined_symm g (lift e)))) wlk
end WildExact
