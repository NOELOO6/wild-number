import Recolor
namespace SixColors
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rename (a b x : Nat) := if x == 15 then 15 else (a*x+b)%15
def keys := Std.HashSet.ofList (plans.map fun p => (p.root,p.mask))
def found (r m : Nat) := keys.contains ((r,m))
def normalizedRoot (r : Nat) := if r == 15 then 15 else 0
def shifts (r a : Nat) := if r == 15 then List.range 15 else [(15-(a*r)%15)%15]
def appears (r m : Nat) := units.any fun a => (shifts r a).any fun b =>
  rename a b r == normalizedRoot r && found (normalizedRoot r) (imageMask m a b)
def namesCheck := (List.range 16).all fun r => (List.range 32768).all fun m =>
  size m != 6 || appears r m

theorem every_choice : namesCheck = true := by native_decide
theorem exactly_712 : plans.length = 712 := by native_decide
theorem affine_round_robin : units.all (fun a => (List.range 15).all fun b =>
    let perm := (List.range 16).map (rename a b)
    (List.range 16).all perm.contains && (List.range 16).all fun v => (List.range v).all fun u =>
      let x := rename a b u
      let y := rename a b v
      oldName (min x y) (max x y) == (a*oldName u v+b)%15) = true := by native_decide

theorem every_mask_has_a_plan {r m : Nat} (hr : r < 16) (hm : m < 32768) (hs : size m = 6) :
    ∃ a ∈ units, ∃ b ∈ shifts r a, rename a b r = normalizedRoot r ∧
      found (normalizedRoot r) (imageMask m a b) = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp every_choice r (List.mem_range.mpr hr)) m (List.mem_range.mpr hm)
  simp only [hs,bne_self_eq_false,Bool.false_or] at h
  obtain ⟨a,ha,hh⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,hc⟩ := List.any_eq_true.mp hh
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨a,ha,b,hb,beq_iff_eq.mp h1,h2⟩
theorem listed_of_found {r m : Nat} (h : found r m = true) :
    ∃ p ∈ plans, p.root = r ∧ p.mask = m := by
  unfold found keys at h
  rw [Std.HashSet.contains_ofList] at h
  have hm := List.contains_iff_mem.mp h
  obtain ⟨p,hp,eq⟩ := List.mem_map.mp hm
  exact ⟨p,hp,congrArg Prod.fst eq,congrArg Prod.snd eq⟩
#print axioms every_mask_has_a_plan
end SixColors
