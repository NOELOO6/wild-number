import Counting
namespace WildExact
open Finset WildDeletion
variable {n k : Nat}

def renamed (p : Equiv.Perm (Fin n)) (g : Coloring n k) : Coloring n k where
  paint x y := g.paint (p x) (p y)
  symm _ _ := g.symm _ _
  proper _ _ _ xy xz eq := p.injective (g.proper _ _ _ (fun h => xy (p.injective h)) (fun h => xz (p.injective h)) eq)

theorem upper_back (p : Equiv.Perm (Fin n)) (g : Coloring n k) {b} :
    Upper (renamed p g) b → Upper g b := by
  classical
  rintro ⟨w,legal,size,works⟩
  let line := fun e : Fin n × Fin n => (min (p e.1) (p e.2),max (p e.1) (p e.2))
  refine ⟨w.image line,?_,Finset.card_image_le.trans size,?_⟩
  · intro e he
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
    have ne : p z.1 ≠ p z.2 := fun eq => (legal _ hz).ne (p.injective eq)
    rcases lt_or_gt_of_ne ne with h|h <;> simp [line,h.le,h]
  intro c x y
  have point (u v) (h : (u,v)∈w) : Touch (w.image line) (p u) (p v) := by
    have yes := Finset.mem_image_of_mem line h
    rcases le_total (p u) (p v) with a|a
    · exact Or.inl (by simpa [line,min_eq_left a,max_eq_right a] using yes)
    · exact Or.inr (by simpa [line,min_eq_right a,max_eq_left a] using yes)
  have maps (a b) (e : Joined (renamed p g) w c a b) : Walk (Joined g (w.image line) c) (p a) (p b) := by
    apply Walk.step (.stay _)
    rcases e with (h|h)|⟨ne,col⟩
    · exact Or.inl (point _ _ h)
    · exact Or.inl (point _ _ h).symm
    · exact Or.inr ⟨fun eq => ne (p.injective eq),col⟩
  simpa using (Walk.mapInto p maps (works c (p.symm x) (p.symm y)))

theorem renamed_missing (p : Equiv.Perm (Fin n)) (g : Coloring n n) (x) :
    missingColor (renamed p g) x = missingColor g (p x) := by
  symm
  apply (unique_missing (renamed p g) x).choose_spec.2
  intro u ne
  exact absent_missing g (p x) (p u) (fun e => ne (p.injective e))

def GoodThree (g : Coloring n n) (a b x : Fin n) :=
  g.paint a b ≠ missingColor g x ∧ g.paint a x ≠ missingColor g b ∧ g.paint b x ≠ missingColor g a

theorem pick_three (hn : n%2=1) (room : 6 ≤ n) (g : Coloring n n)
    (a b : Fin n) : ∃ x, x ≠ a ∧ x ≠ b ∧ GoodThree g a b x := by
  classical
  let candidates := ((univ : Finset (Fin n)).erase a).erase b
  have sz : n ≤ candidates.card+2 := by
    have pos := a.isLt
    by_cases eq : a=b
    · subst b; simp [candidates,Finset.card_erase_of_mem]; omega
    · have hb : b∈(univ : Finset (Fin n)).erase a := by simp [Ne.symm eq]
      simp only [candidates,Finset.card_erase_of_mem hb,Finset.card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
      omega
  let banned := fun (i : Fin 3) (x : Fin n) =>
    if i=0 then g.paint a b = missingColor g x else
    if i=1 then g.paint a x = missingColor g b else g.paint b x = missingColor g a
  let bad := fun i => candidates.filter (banned i)
  have cap (i : Fin 3) : (bad i).card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨xa,xb⟩ := Finset.mem_filter.mp hx
    obtain ⟨ya,yb⟩ := Finset.mem_filter.mp hy
    have good (z) (hz : z∈candidates) : z ≠ a ∧ z ≠ b :=
      ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1,(Finset.mem_erase.mp hz).1⟩
    by_cases z : i=0
    · simp [bad,banned,z] at xb yb
      exact missing_injective hn g (xb.symm.trans yb)
    by_cases o : i=1
    · simp [bad,banned,z,o] at xb yb
      exact g.proper a x y (good x xa).1.symm (good y ya).1.symm (xb.trans yb.symm)
    · simp [bad,banned,z,o] at xb yb
      exact g.proper b x y (good x xa).2.symm (good y ya).2.symm (xb.trans yb.symm)
  apply Classical.byContradiction
  intro no
  have sub : candidates ⊆ bad 0 ∪ bad 1 ∪ bad 2 := by
    intro x hx
    have nae := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have nbe := (Finset.mem_erase.mp hx).1
    have h : ¬ GoodThree g a b x := fun ok => no ⟨x,nae,nbe,ok⟩
    simp only [GoodThree,not_and_or,not_not] at h
    simpa [bad,banned,hx,or_assoc] using h
  have card := Finset.card_le_card sub
  have u := Finset.card_union_le (bad 0 ∪ bad 1) (bad 2)
  have v := Finset.card_union_le (bad 0) (bad 1)
  have := cap 0; have := cap 1; have := cap 2
  omega

theorem normalize_three [NeZero n] (hn : n%2=1) (room : 6≤n) (g : Coloring n n) :
    ∃ p : Equiv.Perm (Fin n), GoodThree (renamed p g) (atIndex n 0) (atIndex n 1) (atIndex n 2) := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let d : Fin n := ⟨2,by omega⟩
  obtain ⟨x,xa,xb,good⟩ := pick_three hn room g a b
  let p := Equiv.swap d x
  have ad : a≠d := by intro h; have z := congrArg Fin.val h; simp [a,b,d] at z
  have bd : b≠d := by intro h; have z := congrArg Fin.val h; simp [a,b,d] at z
  have aa := Equiv.swap_apply_of_ne_of_ne ad xa.symm
  have bb := Equiv.swap_apply_of_ne_of_ne bd xb.symm
  have small (i : Nat) (h : i<n) : (atIndex n i).val=i := Nat.mod_eq_of_lt h
  have e0 : atIndex n 0=a := Fin.ext (small 0 (by omega))
  have e1 : atIndex n 1=b := Fin.ext (small 1 (by omega))
  have e2 : atIndex n 2=d := Fin.ext (small 2 (by omega))
  refine ⟨p,?_⟩
  simp only [e0,e1,e2,GoodThree,renamed_missing]
  change g.paint (p a) (p b) ≠ missingColor g (p d) ∧ g.paint (p a) (p d) ≠ missingColor g (p b) ∧ g.paint (p b) (p d) ≠ missingColor g (p a)
  simp only [p,aa,bb,Equiv.swap_apply_left]
  exact good
end WildExact
