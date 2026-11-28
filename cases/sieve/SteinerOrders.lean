import SparseOrders
import SteinerSystem

namespace WildSieve.Sparse
open Finset WildExact WildSteiner
local instance (priority := 2000) steinerFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

private theorem third_of_closed {n : Nat} (g : Coloring n n) (odd : n%2=1)
    (S : System (Fin n)) (paint : ∀ x y,x≠y → g.paint x y=missingColor g (S.third x y))
    (x y z : Fin n) (xy : x≠y) (xz : x≠z) (yz : y≠z) (c : Fin n)
    (cl : Closed (mate (augment odd g) c) {Fin.last n,x.castSucc,y.castSucc,z.castSucc}) :
    S.third x y=z := by
  classical
  let r := Fin.last n
  let m := mate (augment odd g) c
  have inv : Function.Involutive m := mate_involutive _ _
  have side (p q t : Fin n) (pq : p≠q) (qt : q≠t)
      (closed : Closed m {r,p.castSucc,q.castSucc,t.castSucc}) (rp : m r=p.castSucc) :
      S.third q t=p := by
    have fromQ := closed q.castSucc (by simp)
    have nr : m q.castSucc≠r := fun eq => pq (Fin.castSucc_inj.mp (rp.symm.trans (eq ▸ inv q.castSucc)))
    have np : m q.castSucc≠p.castSucc := fun eq => Fin.castSucc_ne_last _ (inv.injective (eq.trans rp.symm))
    have nq : m q.castSucc≠q.castSucc := (mate_spec _ _ _).1.symm
    have toT : m q.castSucc=t.castSucc := by simpa [nr,np,nq] using fromQ
    have rootCol : missingColor g p=c := by
      have edge := (mate_spec (augment odd g) c r).2
      change (augment odd g).paint r (m r)=c at edge
      rw [rp] at edge
      simpa [augment,r] using edge
    have edge := (mate_spec (augment odd g) c q.castSucc).2
    change (augment odd g).paint q.castSucc (m q.castSucc)=c at edge
    rw [toT,augment_paint] at edge
    exact missing_injective odd g ((paint _ _ qt).symm.trans (edge.trans rootCol.symm))
  have root := cl r (by simp [r])
  change m r∈({r,x.castSucc,y.castSucc,z.castSucc}:Finset _) at root
  have moving : m r≠r := (mate_spec _ _ _).1.symm
  simp only [mem_insert,mem_singleton] at root
  rcases root with bad|h|h|h
  · exact (moving bad).elim
  · have q := side x y z xy yz cl h
    exact (S.swap _ _).trans (q ▸ S.again y z)
  · have q := side y x z xy.symm xz (by simpa [insert_comm] using cl) h
    exact q ▸ S.again x z
  · exact side z x y xz.symm xy (by
      have perm : ({r,z.castSucc,x.castSucc,y.castSucc}:Finset _)={r,x.castSucc,y.castSucc,z.castSucc} := by
        ext v;simp [or_assoc,or_left_comm,or_comm]
      rw [perm];exact cl) h

/-- The ordinary rooted cuts of a Steiner coloring form a linear triple
system. A pair belongs to at most its own Steiner line. -/
theorem pair_cap_of_steiner {n : Nat} (odd : n%2=1) (g : Coloring n n) (data : SteinerColoring g) :
    PairCap (coloringFactor (augment odd g)) (Fin.last n) 1 := by
  classical
  obtain ⟨S,paint⟩ := data
  intro x y xr yr yx
  obtain ⟨a,rfl⟩ := before_root x xr
  obtain ⟨b,rfl⟩ := before_root y yr
  have ab : a≠b := fun e => yx (congrArg Fin.castSucc e.symm)
  let line : Finset (Fin (n+1)) := {a.castSucc,b.castSucc,(S.third a b).castSucc}
  apply card_le_one.mpr
  have unique (X : Finset (Fin (n+1))) (mem : X∈rootTriples (coloringFactor (augment odd g)) (Fin.last n))
      (ax : a.castSucc∈X) (bx : b.castSucc∈X) : X=line := by
    obtain ⟨c,hc⟩ := side_mem.mp mem
    obtain ⟨sub,sz,closed⟩ := candidate_mem.mp hc
    have smaller : ({a.castSucc,b.castSucc}:Finset _).card<X.card := by rw [sz];simp [ab]
    obtain ⟨v,vX,out⟩ := exists_mem_not_mem_of_card_lt_card smaller
    have vr : v≠Fin.last n := fun h => (mem_compl.mp (sub vX)) (mem_singleton.mpr h)
    obtain ⟨d,rfl⟩ := before_root v vr
    have ad : a≠d := fun eq => out (by simp [eq])
    have bd : b≠d := fun eq => out (by simp [eq])
    have Xeq : ({a.castSucc,b.castSucc,d.castSucc}:Finset _)=X := by
      apply eq_of_subset_of_card_le (insert_subset ax (insert_subset bx (singleton_subset_iff.mpr vX)))
      simp [sz,ab,ad,bd]
    have cl : Closed (mate (augment odd g) c) {Fin.last n,a.castSucc,b.castSucc,d.castSucc} := by
      have e : ({Fin.last n}:Finset _)∪X={Fin.last n,a.castSucc,b.castSucc,d.castSucc} := by
        rw [←Xeq];ext u;simp [or_assoc,or_left_comm,or_comm]
      rw [e] at closed
      exact closed
    have h := third_of_closed g odd S paint a b d ab ad bd c cl
    simpa [line,h] using Xeq.symm
  intro X hx Y hy
  obtain ⟨hx,ax,bx⟩ := mem_filter.mp hx
  obtain ⟨hy,ay,by'⟩ := mem_filter.mp hy
  exact (unique X hx ax bx).trans (unique Y hy ay by').symm

/-- Orders for which the sparse-triple certificate applies to every
Steiner triple system coloring. -/
theorem exact_steiner {n : Nat} (order : n∈[61,67,69,73,75]) (odd : n%2=1)
    (g : Coloring n n) (data : SteinerColoring g) : Exact g ((2*n+2)/3) := by
  have yes : (n,Bound.pair 1)∈cases := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at order
    rcases order with rfl|rfl|rfl|rfl|rfl <;> decide
  exact exact_of_cap yes odd g (pair_cap_of_steiner odd g data)

#print axioms exact_steiner
end WildSieve.Sparse
