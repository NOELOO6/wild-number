import CutChecks
import LayoutPaths
namespace WildExact.Seventeen
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

private theorem union_bit {α} (xs : List α) (yes : α → Bool) (mask : α → Nat) (v s : Nat) :
    (xs.foldl (fun a x => if yes x then a ||| mask x else a) s).testBit v =
      (s.testBit v || xs.any (fun x => yes x && (mask x).testBit v)) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.any_cons,ih]
    cases eq : yes x <;> simp [eq,Nat.testBit_or,Bool.or_assoc]

theorem encode_bit {n} (p : Fin n → Bool) (x : Fin n) : (encode p).testBit x.val=p x := by
  unfold encode
  rw [union_bit]
  simp only [Nat.zero_testBit,Bool.false_or,Nat.one_shiftLeft,Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨v,_,pv,ve⟩
    exact (Fin.ext ve) ▸ pv
  · intro px; exact ⟨x,List.mem_finRange _,px,rfl⟩

private theorem slice_bit (b : Big) (j : Fin 4) (t : Nat) (v : V) :
    (slice b j t).testBit v.val = (((((t >>> (4*j.val)) &&& 15)%16) <<< (4*j.val)).testBit (slot b v).val) := by
  have get {α : Type} {n} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
  simp only [slice,sliceMap,get,encode_bit]
  rfl

theorem embed_bit (b : Big) (k) (h : k∈allKeys) (v : V) : (embed b k).testBit v.val = k.testBit (slot b v).val := by
  let part := fun (t j : Nat) => ((((t >>> (4*j)) &&& 15)%16) <<< (4*j))
  have split : ∀ (t : Fin 16384) (v : Slot),
      ((part t.val 0).testBit v.val || (part t.val 1).testBit v.val || (part t.val 2).testBit v.val || (part t.val 3).testBit v.val)
       =t.val.testBit v.val := by native_decide
  simp only [embed,Nat.testBit_or,slice_bit]
  exact split ⟨k,(key_facts.2.1 k h).1⟩ (slot b v)

theorem closed_read (f : V → V) (b : Big) (k) (hk : k∈allKeys) :
    fastClosed (closedTable f) (embed b k)=closedOn f (embed b k) := by
  have get {α : Type} {n} (fn : Fin n → α) (i : Fin n) : (Vector.ofFn fn).get i=fn i := Vector.getElem_ofFn i.isLt
  simp only [fastClosed,closedTable,get]
  exact congrArg (closedOn f) (Nat.mod_eq_of_lt (key_facts.2.2 _ _ hk))

theorem key_mem (p : Small) (i j : Block) (h : i<j) : localMask p i j∈localCuts p := by
  have pair : (i,j)∈namedPairs :=
    List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨j,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using h⟩,rfl⟩⟩
  change localMask p i j∈(Vector.ofFn _).get p
  rw [show ∀ (v : Small), (Vector.ofFn (fun p : Small => namedPairs.map fun z => localMask p z.1 z.2)).get v =
    namedPairs.map (fun z => localMask v z.1 z.2) from fun v => Vector.getElem_ofFn v.isLt]
  exact List.mem_map.mpr ⟨(i,j),pair,rfl⟩

theorem read_cut (b : Big) (p : Small) (i j : Block) (h : i<j) (x : V) :
    (embed b (localMask p i j)).testBit x.val = (owner (b,p) x == i || owner (b,p) x == j) := by
  rw [embed_bit _ _ (key_facts.1 p _ (key_mem p i j h)),localMask,encode_bit]
  rfl

private theorem distinct_labels (l : Layout) (i : Block) : ∃ x, owner l x=i := by
  have mem : ∀ k : Block,k∈K17Connectivity.labels := by decide
  obtain ⟨x,_,eq⟩ := List.mem_map.mp ((layout_shape l).mem_iff.mpr (mem i))
  exact ⟨x,eq⟩

theorem loss_iff (f : V → V) (b : Big) (p : Small) :
    Loss f (b,p) ↔ ∃ k∈localCuts p, closedOn f (embed b k)=true := by
  constructor
  · rintro ⟨a,z,ne,h⟩
    let i := owner (b,p) a
    let j := owner (b,p) z
    have ij : i≠j := by simpa [i,j,sameBlock] using ne
    have pick (u v : Block) (lt : u<v) (eq : ∀ x : V, (owner (b,p) x==u || owner (b,p) x==v)=side (b,p) a z x) :
        ∃ k∈localCuts p, closedOn f (embed b k)=true := by
      refine ⟨localMask p u v,key_mem _ _ _ lt,List.all_eq_true.mpr (fun x _ => ?_)⟩
      simp only [read_cut _ _ _ _ lt,eq,beq_iff_eq]
      exact h x
    rcases lt_or_gt_of_ne ij with le|le
    · exact pick i j le (fun _ => rfl)
    · exact pick j i le (fun _ => Bool.or_comm ..)
  · rintro ⟨k,hk,closed⟩
    have ext (v : Small) : localCuts v=namedPairs.map (fun z => localMask v z.1 z.2) := Vector.getElem_ofFn v.isLt
    rw [ext] at hk
    obtain ⟨⟨i,j⟩,pair,rfl⟩ := List.mem_map.mp hk
    have sorted : ∀ x∈namedPairs,x.1<x.2 := by decide
    have lt := sorted (i,j) pair
    obtain ⟨a,ha⟩ := distinct_labels (b,p) i
    obtain ⟨z,hz⟩ := distinct_labels (b,p) j
    refine ⟨a,z,by simp [sameBlock,ha,hz,lt.ne],fun x => ?_⟩
    have test := List.all_eq_true.mp closed x (List.mem_finRange _)
    simpa only [read_cut _ _ _ _ lt,beq_iff_eq,side,sameBlock,ha,hz] using test

/-- A set bit in the enumerator means that some union of two blocks is closed under the matching. -/
theorem bit_loss (f : V → V) (b : Big) (p : Small) : (badBits (closedTable f) b).testBit p.val=true ↔ Loss f (b,p) := by
  rw [badBits,union_bit,loss_iff]
  simp only [Nat.zero_testBit,Bool.false_or,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨k,hk,m,i⟩
    exact ⟨k,List.contains_iff_mem.mp (((key_facts.2.1 k hk).2 p) ▸ i),closed_read f b k hk ▸ m⟩
  · rintro ⟨k,hk,yes⟩
    have key := key_facts.1 p k hk
    exact ⟨k,key,(closed_read f b k key).trans yes,((key_facts.2.1 k key).2 p).trans (List.contains_iff_mem.mpr hk)⟩

end WildExact.Seventeen
