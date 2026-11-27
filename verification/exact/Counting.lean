import Enumerate
namespace WildExact
open Finset WildDeletion

theorem cover_node {n} (fuel) (xs : List (Fin (n+1))) (m : Row n)
    (hm : m ∈ enumerate fuel xs) (v : Fin (n+1)) (hv : v∈xs) :
    ∃ u, rowHas m (v,u)=true := by
  induction fuel generalizing xs m with
  | zero => cases xs <;> simp [enumerate] at hm hv
  | succ d ih =>
    cases xs with
    | nil => simp at hv
    | cons x xs =>
      obtain ⟨y,hy,r⟩ := List.mem_flatMap.mp hm
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp r
      rcases List.mem_cons.mp hv with rfl|tail
      · exact ⟨y,by simp [rowHas]⟩
      by_cases eq : v=y
      · subst v; exact ⟨x,by simp [rowHas]⟩
      obtain ⟨u,yes⟩ := ih _ _ hs (List.mem_filter.mpr ⟨tail,by simpa using eq⟩)
      refine ⟨u,?_⟩
      simp only [rowHas,Bool.or_eq_true,List.contains_iff_mem,List.mem_cons] at yes ⊢
      exact yes.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))

theorem row_equiv {n} (g : Coloring (n+1) n) (c) (m : Row n) (mem : m∈Rows n)
    (res : Respects (mate g c) m) (x y : Fin (n+1)) (ne : x≠y) :
    rowHas m (x,y) = decide (g.paint x y = c) := by
  have sound (u v) (h : rowHas m (u,v)=true) : mate g c u=v := by
    rcases Bool.or_eq_true_iff.mp h with l|r
    · exact res _ (List.contains_iff_mem.mp l)
    · have e := res _ (List.contains_iff_mem.mp r)
      exact (congrArg (mate g c) e).symm.trans (mate_involutive g c v)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact (sound x y h) ▸ (mate_spec g c x).2
  · intro eq
    obtain ⟨u,yes⟩ := cover_node _ _ _ mem x (List.mem_finRange x)
    have same := sound x u yes
    have xy := g.proper x (mate g c x) y (mate_spec g c x).1 ne ((mate_spec g c x).2.trans eq.symm)
    exact same.symm.trans xy ▸ yes

theorem total_add {α} (xs : List α) (f g : α → Int) :
    totalI xs (fun x => f x+g x)=totalI xs f+totalI xs g := by
  induction xs with
  | nil => simp [totalI]
  | cons x xs ih => simp only [totalI,List.map_cons,List.sum_cons] at ih ⊢; omega

theorem total_mono {α} (xs : List α) {f g : α → Int} (le : ∀ x∈xs, f x ≤ g x) :
    totalI xs f ≤ totalI xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact add_le_add (le x (by simp)) (ih (fun y h => le y (by simp [h])))

theorem total_const {α} (xs : List α) (k : Int) : totalI xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [totalI]
  | cons x xs ih => simp [totalI,List.length_cons,Int.add_mul] at ih ⊢; omega

theorem transpose {α β} (xs : List α) (ys : List β) (f : α → β → Int) :
    totalI xs (fun x => totalI ys (f x))=totalI ys (fun y => totalI xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [totalI]
  | cons x xs ih =>
    change totalI ys (f x)+totalI xs _ = totalI ys (fun y => f x y + totalI xs (fun a => f a y))
    rw [total_add,ih]

theorem single_color {n} (c : Fin n) (v : Int) :
    totalI (List.finRange n) (fun y => if c=y then v else 0)=v := by
  classical
  rw [totalI,← List.sum_toFinset _ (List.nodup_finRange n)]
  simp

theorem fees_sum {n} (g : Coloring (n+1) n) (rs : Fin n → Row n)
    (h : ∀ c, rs c∈Rows n ∧ Respects (mate g c) (rs c))
    (ps : List (Price n)) (ne : ∀ p∈ps,p.1.1≠p.1.2) :
    totalI (List.finRange n) (fun c => fee ps (rs c)) = totalI ps Prod.snd := by
  unfold fee
  rw [transpose]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p mem
  have eq (c : Fin n) := row_equiv g c _ (h c).1 (h c).2 p.1.1 p.1.2 (ne _ mem)
  simpa only [eq,decide_eq_true_eq] using (single_color (g.paint p.1.1 p.1.2) p.2)

theorem some_below {α} (xs : List α) (f : α → Int) (k : Int)
    (lt : totalI xs f < xs.length*k) : ∃ x∈xs, f x<k := by
  by_contra! contra
  exact (not_lt_of_ge ((total_const xs k) ▸ total_mono xs (f:=fun _ => k) contra)) lt

theorem all_of_zero {α} (xs : List α) (bad : α → Bool)
    (lt : totalI xs (fun x => if bad x then 1 else 0)<1) : ∀ x∈xs,bad x=false := by
  have nonneg (ys : List α) : 0 ≤ totalI ys (fun x => if bad x then 1 else 0) := by
    have := total_mono ys (f:=fun _ => 0) (g:=fun x => if bad x then 1 else 0)
      (fun x _ => by cases h : bad x <;> simp [h])
    simpa [total_const] using this
  induction xs with
  | nil => simp
  | cons a xs ih =>
    change (if bad a then (1:Int) else 0) + totalI xs _ < 1 at lt
    have h := nonneg xs
    cases eq : bad a <;> simp [eq] at lt
    · intro y hy; rcases List.mem_cons.mp hy with rfl|mem
      · exact eq
      · exact ih lt _ mem
    · omega
end WildExact
