import ThreeStars
namespace ThreeStars
open VertexRedraw Teams

private def addHits (t : Array Nat) (ss : List Nat) (w : Nat) :=
  ss.foldl (fun a s => a.modify s (·+w)) t
private theorem hit_size (t : Array Nat) (ss : List Nat) (w) : (addHits t ss w).size=t.size := by
  induction ss generalizing t with
  | nil => rfl
  | cons a l ih => simpa [addHits] using ih (t.modify a (·+w))
private theorem hit_value (t : Array Nat) (ss : List Nat) (w s) (h : s<t.size) :
    lookup (addHits t ss w) s = lookup t s + ss.count s*w := by
  induction ss generalizing t with
  | nil => simp [addHits]
  | cons x xs ih =>
    have h' : s<(t.modify x (·+w)).size := by simpa using h
    change lookup (addHits (t.modify x (·+w)) xs w) s = _
    rw [ih _ h']
    by_cases hx : x=s
    · subst x
      simp [lookup,Array.getElem?_modify,Array.getElem?_eq_getElem h,Nat.add_mul,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm]
    · simp [lookup,Array.getElem?_modify,hx,List.count_cons,beq_iff_eq,Ne.symm hx]

private theorem accumulated (gs : List Layout) (t : Array Nat) (s) (h : s<t.size) :
    lookup (gs.foldl record t) s = lookup t s + total gs (fun g => (sides g).count s*g.weight) := by
  induction gs generalizing t with
  | nil => simp [total]
  | cons g gs ih =>
    have size : (record t g).size = t.size := hit_size t (sides g) g.weight
    change lookup (gs.foldl record (record t g)) s = _
    rw [ih _ (by simpa [size] using h)]
    have val : lookup (record t g) s = _ := hit_value t (sides g) g.weight s h
    rw [val,total_cons]; omega

theorem ledger_value (gs : List Layout) (s : Nat) (h : s<65536) :
    lookup (ledger gs) s = total gs (fun g => (sides g).count s*g.weight) := by
  have val := accumulated gs (Array.replicate 65536 0) s (by simpa using h)
  simpa [ledger,lookup,Array.getElem?_replicate,h] using val

def spoils (g : Layout) (m : R) := (subsets m).any (sides g).contains

private theorem subsets_small (m : R) (s) (hs : s∈subsets m) : s<65536 := by
  induction m generalizing s with
  | nil => have eq : s=0 := by simpa [subsets] using hs
           omega
  | cons e es ih =>
    rcases List.mem_append.mp hs with h|h
    · exact ih _ h
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      have bits : ∀ (a b : V), (2^a.val ||| 2^b.val)<65536 := by decide
      exact Nat.or_lt_two_pow (n:=16) (ih _ ha) (bits e.1 e.2)

theorem loss_bounded (gs : List Layout) (m : R) :
    total gs (fun g => if spoils g m then g.weight else 0) ≤ spent (ledger gs) m := by
  let f := fun (g : Layout) (s : Nat) => (sides g).count s*g.weight
  have h (g : Layout) : (if spoils g m then g.weight else 0) ≤ total (subsets m) (f g) := by
    cases eq : spoils g m with
    | false => simp
    | true =>
      obtain ⟨s,hs,yes⟩ := List.any_eq_true.mp eq
      have mem := List.contains_iff_mem.mp yes
      have pos : 0<(sides g).count s := List.count_pos_iff.mpr mem
      have low := FiveColors.coveredWeight (subsets m) ((sides g).contains ·) g.weight ⟨s,hs,yes⟩
      refine Nat.le_trans (by simpa using low) (total_mono _ _ _ ?_)
      intro v _
      by_cases hv : (sides g).contains v = true
      · have count := List.count_pos_iff.mpr (List.contains_iff_mem.mp hv)
        exact (by simpa [List.contains_iff_mem.mp hv,f] using Nat.mul_le_mul_right g.weight (show 1≤(sides g).count v from count))
      · have miss : v ∉ sides g := fun h => hv (List.contains_iff_mem.mpr h)
        simp [miss]
  have upper := total_mono gs _ _ (fun g _ => h g)
  rw [transpose] at upper
  exact Nat.le_trans upper (total_mono _ _ _ (fun s hs => Nat.le_of_eq (ledger_value gs s (subsets_small m s hs)).symm))

private theorem masked_bit (s n : Nat) : s &&& 2^n = if s.testBit n then 2^n else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases same : n=i
  · subst i; cases h : s.testBit n <;> simp [Nat.testBit_and,Nat.testBit_two_pow,h]
  · cases h : s.testBit n <;> simp [Nat.testBit_and,Nat.testBit_two_pow,h,same]

theorem sealed_mem {s : Nat} (m : R)
    (agree : ∀ e∈m, s.testBit e.1.val = s.testBit e.2.val) : s &&& full m ∈ subsets m := by
  induction m with
  | nil => simp [full,subsets]
  | cons e es ih =>
    have tail := ih (fun a ha => agree a (by simp [ha]))
    have eq := agree e (by simp)
    change s &&& (full es ||| mask e) ∈ subsets es ++ _
    rw [Nat.and_or_distrib_left]
    unfold mask
    rw [Nat.and_or_distrib_left,masked_bit,masked_bit,eq]
    cases bit : s.testBit e.2.val with
    | false => simpa [bit] using List.mem_append_left ((subsets es).map (· ||| mask e)) tail
    | true => exact List.mem_append_right _ (List.mem_map.mpr ⟨_,tail,by simp [mask]⟩)

theorem sealed_full {s : Nat} (small : s<65536) (m : R) (complete : full m=65535)
    (agree : ∀ e∈m, s.testBit e.1.val = s.testBit e.2.val) : s∈subsets m := by
  have h := sealed_mem m agree
  rw [complete,show 65535=2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt small] at h
  exact h
end ThreeStars
