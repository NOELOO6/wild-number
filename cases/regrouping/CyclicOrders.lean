import RoundRobin
import Reflection
import StarDraw

namespace WildExact.Periodic
open Finset WildDeletion WildExact.Reflection WildSieve

private def offset (p : Fin 3) := if p=0 then 0 else p.val+3

private theorem offset_port (p : Fin 3) : Port (offset p) := by
  rcases p with ⟨p,h⟩
  rcases (show p=0 ∨ p=1 ∨ p=2 by omega) with rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem bounded_port {a : Nat} (pa : Port a) : a≤5 := by
  rcases pa with rfl|rfl|rfl <;> decide

private theorem offset_mod (p : Fin 3) : offset p%3=p.val := by
  by_cases h : p=0
  · simp [offset,h]
  · simp only [offset,if_neg h]
    have := p.isLt
    omega

private theorem port_index {a : Nat} (pa : Port a) : ∃ p : Fin 3,offset p=a := by
  rcases pa with rfl|rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

/-- The regular triples are {3i,3i+4,3i+5}. The complementary vertices
form one group of size four or five. -/
theorem defect_upper (n k : Nat) [NeZero n] (order : n=3*k+4 ∨ n=3*k+5) :
    Upper (roundRobin n) ((2*n+2)/3) := by
  classical
  let point (i : Fin k) (p : Fin 3) : Fin n := ⟨3*i.val+offset p,by
    have := i.isLt
    have := bounded_port (offset_port p)
    omega⟩
  let group (i : Fin k) := univ.image (point i)
  have coords {i j : Fin k} {p q : Fin 3} (eq : point i p=point j q) : i=j ∧ p=q := by
    have z := congrArg Fin.val eq
    change 3*i.val+offset p=3*j.val+offset q at z
    have x := offset_mod p
    have y := offset_mod q
    have pq : p=q := Fin.ext (by omega)
    subst q
    exact ⟨Fin.ext (by omega),rfl⟩
  have count (i : Fin k) : (group i).card=3 := by
    rw [show group i=univ.image (point i) from rfl,card_image_of_injective _ (fun _ _ eq => (coords eq).2),card_univ,Fintype.card_fin]
  let used := univ.biUnion group
  have usedSize : used.card=3*k := by
    rw [show used=univ.biUnion group from rfl,card_biUnion]
    · simp [count,Nat.mul_comm]
    · intro i _ j _ ne
      apply disjoint_left.mpr
      intro v vi vj
      obtain ⟨p,_,xp⟩ := mem_image.mp vi
      obtain ⟨q,_,xq⟩ := mem_image.mp vj
      exact ne (coords (xp.trans xq.symm)).1
  let fixed := usedᶜ
  have fixedSize : fixed.card=n-3*k := by simp [fixed,card_compl,usedSize]
  obtain ⟨root,rootIn⟩ := card_pos.mp (show 0<fixed.card by rw [fixedSize]; omega)
  let w := spokes fixed ∪ univ.biUnion (fun i => spokes (group i))
  refine ⟨w,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with h|h
    · exact spokes_legal _ e h
    obtain ⟨i,_,eh⟩ := mem_biUnion.mp h
    exact spokes_legal _ e eh
  · have a := spokes_bound fixed
    rw [fixedSize] at a
    have b : (univ.biUnion (fun i => spokes (group i))).card≤2*k := by
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _ : Fin k,2 := sum_le_sum (fun i _ => by simpa [count] using spokes_bound (group i))
        _ = _ := by simp [Nat.mul_comm]
    exact (card_union_le _ _).trans (by omega)
  intro c
  let E := Joined (roundRobin n) w c
  let hit := Walk E root
  have liftWild {v u : Fin n} (h : Walk (Touch w) v u) : Walk E v u :=
    Walk.mapInto (E:=Touch w) (F:=E) id (fun a _ edge => Walk.step (.stay a) (Or.inl edge)) h
  have fixedHit (v) (hv : v∈fixed) : hit v :=
    liftWild (in_star (subset_union_left : spokes fixed⊆w) rootIn hv)
  have member (i : Fin k) (p : Fin 3) : point i p∈group i := mem_image.mpr ⟨p,mem_univ _,rfl⟩
  have move (i : Fin k) (p q : Fin 3) : Walk E (point i p) (point i q) := by
    apply liftWild
    apply in_star _ (member i p) (member i q)
    intro e he
    exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,he⟩)
  have all (x : Fin n) : hit x := by
    apply Classical.byContradiction
    intro missed
    let I := (univ.filter (fun i : Fin k => ¬ hit (point i 0))).image Fin.val
    have unhit {v : Fin n} (nv : ¬hit v) :
        ∃ j : Fin k, j.val∈I ∧ ∃ p : Fin 3,point j p=v := by
      have usedV : v∈used := by
        apply Classical.byContradiction
        intro h
        exact nv (fixedHit v (mem_compl.mpr h))
      obtain ⟨j,_,gj⟩ := mem_biUnion.mp usedV
      obtain ⟨p,_,pv⟩ := mem_image.mp gj
      refine ⟨j,mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩,p,pv⟩
      intro reaches
      exact nv (pv ▸ reaches.join (move j 0 p))
    obtain ⟨j,jI,_⟩ := unhit missed
    apply no_cyclic_reflection n c.val (by omega) I ⟨j.val,jI⟩
    · intro i hi
      obtain ⟨i,_,rfl⟩ := mem_image.mp hi
      have := i.isLt
      omega
    intro i hi a pa
    obtain ⟨i,ih,rfl⟩ := mem_image.mp hi
    obtain ⟨p,rfl⟩ := port_index pa
    let v := point i p
    have no : ¬ hit v := fun reaches => (mem_filter.mp ih).2 (reaches.join (move i p 0))
    let z := if v.val≤c.val then c.val-v.val else n+c.val-v.val
    have zb : z<n := by dsimp [z]; split <;> have := c.isLt <;> have := v.isLt <;> omega
    let y : Fin n := ⟨z,zb⟩
    have sumEq : v.val+y.val=if v.val≤c.val then c.val else n+c.val := by
      change v.val+z=_
      dsimp [z]
      split <;> have := v.isLt <;> omega
    have link : Walk E v y := by
      by_cases eq : v=y
      · exact eq ▸ Walk.stay _
      apply Walk.step (E:=E) (.stay _) (Or.inr ⟨eq,?_⟩)
      apply Fin.ext
      change (v.val+y.val)%n=c.val
      rw [sumEq]
      split
      · exact Nat.mod_eq_of_lt c.isLt
      · simp [Nat.add_mod,Nat.mod_eq_of_lt c.isLt]
    have noY : ¬hit y := fun reached => no (reached.join (backwards (joined_symm _) link))
    obtain ⟨q,qI,r,yq⟩ := unhit noY
    refine ⟨q.val,qI,offset r,offset_port r,?_⟩
    rw [← yq] at sumEq
    exact sumEq
  exact fun x y => (backwards (joined_symm _) (all x)).join (all y)

private theorem move_order {n m : Nat} [NeZero n] [NeZero m] (eq : n=m) (b) :
    Exact (roundRobin m) b → Exact (roundRobin n) b := by subst m; exact id

/-- The standard round-robin coloring attains the conjectured value at
every odd order at least three. -/
theorem round_robin_odd (n : Nat) [NeZero n] (lo : 3≤n) (odd : n%2=1) :
    Exact (roundRobin n) ((2*n+2)/3) := by
  by_cases zero : n%3=0
  · have eq : n=3*(n/3) := by omega
    have nz : 0<n/3 := by omega
    haveI : NeZero (3*(n/3)) := ⟨by omega⟩
    have h := round_robin_triples (n/3) (by omega)
    have value : (2*n+2)/3=2*(n/3) := by omega
    rw [value]
    exact move_order eq _ h
  · exact exact_of_upper (defect_upper n (n/3-1) (by have := Nat.mod_add_div n 3; omega)) (fun _ => odd_lower lo _)

#print axioms round_robin_odd
end WildExact.Periodic
