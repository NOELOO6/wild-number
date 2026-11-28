import CycleFamilies

namespace WildExact.SwitchFamily
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def rowPasses (i : Nat) :=
  let d := families[i]!
  d.n == (if i==0 then 15 else 2*i+17) && dataOK d &&
    checkSize d d.n && checkSize d (d.n+1)

theorem all_rows : families.size=30 ∧ (List.range 30).all rowPasses=true := by native_decide

private theorem row_info (i : Fin 30) : let d := families[i.val]!
    d.n=(if i.val==0 then 15 else 2*i.val+17) ∧ checkSize d d.n=true ∧ checkSize d (d.n+1)=true := by
  have h := List.all_eq_true.mp all_rows.2 i.val (List.mem_range.mpr i.isLt)
  simpa [rowPasses,Bool.and_eq_true,and_assoc] using
    (show ((families[i.val]!).n == (if i.val==0 then 15 else 2*i.val+17))=true ∧
      checkSize families[i.val]! (families[i.val]!).n=true ∧ checkSize families[i.val]! ((families[i.val]!).n+1)=true from
      ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1,
       (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2,(Bool.and_eq_true_iff.mp h).2⟩)

private theorem checked_of_size {v : Nat} [NeZero v] (d : Family) (pass : checkSize d v=true) :
    checked (scheme d v) ((2*d.n+2)/3)=true := by
  simpa [checkSize,Nat.pos_of_ne_zero (NeZero.ne v)] using pass

/-- At every listed order any minimum coloring realizing the specified cycle choices reaches the lower bound. -/
theorem exact_family (i : Fin 30) : let d := families[i.val]!
    (∀ g : Coloring d.n d.n, Realizes g (scheme d d.n) → Exact g ((2*d.n+2)/3)) ∧
    (∀ g : Coloring (d.n+1) d.n, Realizes g (scheme d (d.n+1)) → Exact g ((2*d.n+2)/3)) := by
  let d := families[i.val]!
  obtain ⟨ord,odd,even⟩ := row_info i
  have lo : 3≤d.n := by dsimp only [d]; split at ord <;> omega
  letI : NeZero d.n := ⟨by omega⟩
  constructor
  · intro g fit
    exact exact_of_upper (upper_of_scheme g _ _ fit (checked_of_size d odd)) (fun _ => odd_lower lo g)
  · intro g fit
    exact exact_of_upper (upper_of_scheme g _ _ fit (checked_of_size d even)) (fun _ => even_lower (n:=d.n) (Nat.le_succ_of_le lo) g)

#print axioms exact_family
end WildExact.SwitchFamily
