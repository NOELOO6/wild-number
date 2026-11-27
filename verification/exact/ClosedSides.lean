import StatsProof
import ThirdState

namespace WildExact.Seventeen
open WildExact
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def edgeUnion (r : Row 17) := (masks r).foldr (· ||| ·) 0

private theorem unionBit (r : Row 17) (k : Nat) :
    (edgeUnion r).testBit k = r.any (fun e => k == e.1.val || k == e.2.val) := by
  induction r with
  | nil => simp [edgeUnion,masks]
  | cons e r ih =>
    change ((edgeMask e) ||| edgeUnion r).testBit k = _
    simp only [edgeMask,Nat.testBit_or,Nat.one_shiftLeft,Nat.testBit_two_pow,ih,List.any_cons]
    simp only [Bool.beq_eq_decide_eq]
    simp only [eq_comm (a := e.1.val) (b := k),eq_comm (a := e.2.val) (b := k)]

private theorem chosen_mem (pred : V × V → Bool) (r : Row 17) :
    edgeUnion (r.filter pred) ∈ unions (r.filter pred).length (masks r) := by
  induction r with
  | nil => simp [edgeUnion,masks,unions]
  | cons e r ih =>
    cases h : pred e
    · simp only [List.filter_cons,h,Bool.false_eq_true,if_false]
      cases n : (List.filter pred r).length with
      | zero => rw [n] at ih; simpa [unions] using ih
      | succ k => rw [n] at ih; exact List.mem_append_right _ ih
    · simp only [List.filter_cons,h,if_true,List.length_cons]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih,rfl⟩)

theorem candidates_bounded (r : Row 17) (s : Nat) (h : s∈candidates r) : s<262144 := by
  have edges : ∀ e : V × V, edgeMask e < 2^18 := by native_decide
  have bound (k : Nat) (xs : List Nat) (good : ∀ x∈xs,x<2^18) (s : Nat) (hs : s∈unions k xs) : s<2^18 := by
    induction xs generalizing k s with
    | nil => cases k <;> simp [unions] at hs; subst s; decide
    | cons a xs ih =>
      cases k with
      | zero => simp [unions] at hs; subst s; decide
      | succ k =>
        rcases List.mem_append.mp hs with yes|yes
        · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp yes
          exact Nat.or_lt_two_pow (good a (by simp)) (ih k (fun x h => good x (by simp [h])) _ hb)
        · exact ih _ (fun x h => good x (by simp [h])) _ yes
  have mem : ∀ a∈masks r,a<2^18 := by
    intro a ha; obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha; exact edges e
  rcases List.mem_append.mp h with a|a
  · rcases List.mem_append.mp a with b|b
    exacts [bound _ _ mem s b,bound _ _ mem s b]
  · exact bound _ _ mem s a

private theorem side_size (l : Layout) {s : Nat} (hs : s∈sides l) :
    s<262144 ∧ ((List.finRange 18).filter (fun x => s.testBit x.val)).length ∈ [4,6,8] := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hs
  have bound := key_facts.2.2 l.1 k (key_facts.1 l.2 k hk)
  refine ⟨bound,?_⟩
  have ext (p : Small) : localCuts p = namedPairs.map (fun z => localMask p z.1 z.2) := Vector.getElem_ofFn p.isLt
  rw [ext] at hk
  obtain ⟨⟨i,j⟩,ij,rfl⟩ := List.mem_map.mp hk
  have sorted : ∀ q∈namedPairs,q.1<q.2 := by decide
  have h := ((layout_shape l).filter (fun b => b==i || b==j)).length_eq
  simp only [List.filter_map,List.length_map] at h
  have sizes : ∀ q∈namedPairs,(K17Connectivity.labels.filter (fun b => b==q.1 || b==q.2)).length∈[4,6,8] := by decide
  simpa only [read_cut _ _ _ _ (sorted _ ij),Function.comp_def,←h] using sizes (i,j) ij

private theorem colorCount (r : Row 17) (p : V → Bool) (closed : ∀ e ∈ r, p e.1 = p e.2) :
    ((K17Connectivity.ends r).filter p).length = 2*(r.filter (fun e => p e.1)).length := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    have eq := closed e (by simp)
    have rest := ih (fun e h => closed e (by simp [h]))
    cases e with
    | mk a b =>
      change p a=p b at eq
      cases yes : p a <;> simp [K17Connectivity.ends,List.filter_cons,←eq,yes] at rest ⊢ <;> omega

/-- If a color closes off a pair of blocks, that side is a union of two, three or four of its matching edges. -/
theorem side_in_matching (l : Layout) (f : V → V) (r : Row 17) (rel : Respects f r)
    (full : (K17Connectivity.ends r).Perm (List.finRange 18)) {s : Nat} (hs : s∈sides l)
    (sealed : closedOn f s=true) : s∈candidates r := by
  let mark := fun x : V => s.testBit x.val
  let take := fun e : V × V => mark e.1
  have closed (e) (he : e∈r) : mark e.1=mark e.2 := by
    have yes := eq_of_beq (List.all_eq_true.mp sealed e.1 (List.mem_finRange _))
    simpa only [mark,rel e he] using yes
  obtain ⟨small,sz⟩ := side_size l hs
  have lengthEq := (full.filter mark).length_eq
  rw [colorCount r mark closed] at lengthEq
  have sizes : (r.filter take).length=2 ∨ (r.filter take).length=3 ∨ (r.filter take).length=4 := by
    change 2*(r.filter take).length=((List.finRange 18).filter (fun x => s.testBit x.val)).length at lengthEq
    have alt : ∀ n : Nat, n∈[4,6,8] → n=4 ∨ n=6 ∨ n=8 := fun n h => by simpa using h
    rcases alt _ sz with h|h|h <;> omega
  have same : edgeUnion (r.filter take)=s := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [unionBit]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,List.mem_filter,Bool.or_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨e,⟨he,one⟩,equal|equal⟩
      · simpa only [equal] using one
      · simpa only [equal] using (closed e he).symm.trans one
    · intro one
      have below : k<18 := by
        apply Nat.lt_of_not_ge
        intro hi
        have lo : s<2^k := lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0<2) hi)
        rw [Nat.testBit_lt_two_pow lo] at one
        exact Bool.noConfusion one
      let x : V := ⟨k,below⟩
      obtain ⟨e,he,hx⟩ := List.mem_flatMap.mp (full.mem_iff.mpr (List.mem_finRange x))
      rcases e with ⟨a,b⟩
      change x∈[a,b] at hx
      rcases List.mem_cons.mp hx with xa|xb
      · exact ⟨(a,b),⟨he,xa ▸ one⟩,Or.inl (congrArg Fin.val xa)⟩
      · have xb := List.mem_singleton.mp xb
        exact ⟨(a,b),⟨he,(closed (a,b) he).trans (xb ▸ one)⟩,Or.inr (congrArg Fin.val xb)⟩
  have mem := chosen_mem take r
  rw [same] at mem
  rcases sizes with n|n|n <;> rw [n] at mem
  · exact List.mem_append_left _ (List.mem_append_left _ mem)
  · exact List.mem_append_left _ (List.mem_append_right _ mem)
  · exact List.mem_append_right _ mem

end WildExact.Seventeen
