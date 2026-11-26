import ThreeStars
namespace ThreeStars
open VertexRedraw EdgeWalk Teams

theorem represent (k : K) (c : C) (f : V → V) (inv : ∀ x, f (f x)=x)
    (ne : ∀ x, f x≠x) (agree : respects f (required k c)) :
    ∃ m∈candidates k c, respects f m := by
  have closed : ∀ x∈unused k c, f x∈unused k c := by
    intro x hx
    have miss := (List.mem_filter.mp hx).2
    refine List.mem_filter.mpr ⟨(by decide : ∀ x : V, x∈points) _,?_⟩
    rw [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨e,he,hit⟩ := List.any_eq_true.mp yes
    have mate := agree e he
    have back : f e.2=e.1 := by rw [←mate,inv]
    have endp : e.1=x ∨ e.2=x := by
      rcases Bool.or_eq_true_iff.mp hit with a|b
      · exact Or.inr (by rw [←mate,beq_iff_eq.mp a,inv])
      · exact Or.inl (by rw [←back,beq_iff_eq.mp b,inv])
    have bad : ((required k c).any (fun e => e.1==x || e.2==x)) = true :=
      List.any_eq_true.mpr ⟨e,he,by rcases endp with left|right <;> simp [*]⟩
    simp [bad] at miss
  have len : (unused k c).length ≤ 16 :=
    Nat.le_trans (List.length_filter_le _ _) (by decide : points.length≤16)
  obtain ⟨m,hm,ok⟩ := fills_complete f inv ne 16 _ len closed
  exact ⟨_,List.mem_map.mpr ⟨m,hm,rfl⟩,fun e he =>
    (List.mem_append.mp he).elim (agree e) (ok e)⟩

private theorem perm_total {α} {xs ys : List α} (p : xs.Perm ys) (v : α → Nat) :
    total xs v = total ys v := by
  induction p with
  | nil => rfl
  | cons a _ ih => simp only [total_cons,ih]
  | swap a b xs => simp only [total_cons]; omega
  | trans _ _ ih jh => exact ih.trans jh

private theorem support_bound {α : Type} [DecidableEq α] (xs ys : List α)
    (v : α → Nat) (unique : xs.Nodup) (available : ∀ e∈xs, e∈ys ∨ v e=0) :
    total xs v ≤ total ys v := by
  induction xs generalizing ys with
  | nil => simp [total]
  | cons a xs ih =>
    have dis := List.nodup_cons.mp unique
    by_cases hy : a∈ys
    · have eq := perm_total (List.perm_cons_erase hy) v
      rw [eq,total_cons,total_cons]
      apply Nat.add_le_add_left
      apply ih (ys.erase a) dis.2
      intro x hx
      exact (available x (by simp [hx])).imp_left ((List.mem_erase_of_ne
        (show x≠a from fun h => dis.1 (h ▸ hx))).mpr)
    · have zero := (available a (by simp)).resolve_left hy
      simpa only [total_cons,zero,Nat.zero_add] using
        (show 0+total xs v ≤ total ys v by simpa using ih ys dis.2 (fun x hx => available x (by simp [hx])))

private theorem total_append {α} (a b : List α) (f : α → Nat) :
    total (a++b) f=total a f+total b f := by
  induction a with
  | nil => simp [total]
  | cons x xs ih => simp only [List.cons_append,total_cons,ih]; omega
private theorem flat_total {α β} (xs : List α) (m : α→List β) (f : β→Nat) :
    total (xs.flatMap m) f = total xs (fun c => total (m c) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,total_append,total_cons,ih]

theorem fees_bounded (k : K) (m : C → R) (f : C → V → V)
    (proper : ∀ i j x, f i x=f j x → i=j)
    (respect : ∀ c, respects (f c) (m c)) (regs : ∀ c, regular (m c)=true) :
    total colors (fun c => total (m c) (fee k)) ≤ total entries (fee k) := by
  rw [←flat_total]
  apply support_bound
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro c _
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (regs c)).2
    · have dis : colors.Nodup := by decide
      apply dis.imp
      intro c d different a ha b hb eq
      subst b
      exact different (proper c d a.1 ((respect c a ha).trans (respect d a hb).symm))
  · intro e he
    obtain ⟨c,_,hm⟩ := List.mem_flatMap.mp he
    have order := of_decide_eq_true (List.all_eq_true.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (regs c)).1).2 e hm)
    by_cases small : e.2.val<12
    · exact Or.inl ((by decide : ∀ a b : V, a<b → b.val<12 → (a,b)∈entries) e.1 e.2 order small)
    · exact Or.inr (by simp [fee,small])
end ThreeStars
