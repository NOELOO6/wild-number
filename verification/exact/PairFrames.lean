import RootedMatching
import Counting
import PairData

namespace WildExact.Seventeen
open WildExact

def moveToTarget (x : V) : Equiv.Perm V :=
  if first x=target then Equiv.swap x target
  else (Equiv.swap x target).trans (Equiv.swap (first x) (first target))

theorem visit_sound {n} (allowed : Fin (n+1) → Fin (n+1) → Bool) (test : Row n → Bool)
    (fuel) (xs : List (Fin (n+1))) (acc m : Row n) (member : m ∈ enumerate fuel xs)
    (ok : ∀ e∈m, allowed e.1 e.2=true) (checked : visit allowed test fuel xs acc=true) :
    test (m.reverse ++ acc)=true := by
  induction fuel generalizing xs acc m with
  | zero => cases xs <;> simp [enumerate] at member
            subst m; exact checked
  | succ k ih =>
    cases xs with
    | nil => simp [enumerate] at member; subst m; exact checked
    | cons x xs =>
      obtain ⟨y,hy,z⟩ := List.mem_flatMap.mp member
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp z
      have choose := List.all_eq_true.mp checked y hy
      have edge := ok (x,y) (by simp)
      simp only [edge,Bool.not_true,Bool.false_or] at choose
      simpa using ih _ ((x,y)::acc) r hr (fun e h => ok e (by simp [h])) choose

theorem lookup_agrees (f : V → V) (inv : Function.Involutive f) (r : Row 17)
    (res : Respects f r) (v : V) (covered : ∃ e∈r, e.1=v ∨ e.2=v) : lookup r v=f v := by
  induction r with
  | nil => simp at covered
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    have ab := res (a,b) (by simp)
    change f a=b at ab
    by_cases va : v=a
    · subst v; simpa [lookup] using ab.symm
    by_cases vb : v=b
    · subst v; simp [lookup,va,← ab,inv a]
    apply (show lookup ((a,b)::es) v=lookup es v by simp [lookup,va,vb]).trans
    apply ih (fun e h => res e (by simp [h]))
    obtain ⟨e,mem,h⟩ := covered
    rcases List.mem_cons.mp mem with rfl|t
    · exact False.elim (h.elim (fun h => va h.symm) (fun h => vb h.symm))
    · exact ⟨e,t,h⟩

private theorem witness_perm (m : Table) (w : Witness) (yes : validates m w=true) :
    ∃ q : Equiv.Perm V, q root=root ∧ (∀ x,q (first x)=first (q x)) ∧
      ∀ x,q (entry (canon w.kind).2 x)=m.get (q x) := by
  obtain ⟨rt,all⟩ := Bool.and_eq_true_iff.mp yes
  have localFact (v : V) : w.inverse.get (w.perm.get v) = v ∧ w.perm.get (w.inverse.get v) = v ∧
      w.perm.get (first v) = first (w.perm.get v) ∧ w.perm.get (entry (canon w.kind).2 v) = m.get (w.perm.get v) := by
    have z := List.all_eq_true.mp all v (List.mem_finRange _)
    have get {α : Type} {n} (fn : Fin n → α) (i : Fin n) : (Vector.ofFn fn).get i=fn i := Vector.getElem_ofFn i.isLt
    simpa only [refA,refB,get,Bool.and_eq_true,beq_iff_eq,and_assoc] using z
  let q : Equiv.Perm V := ⟨w.perm.get,w.inverse.get,fun v => (localFact v).1,fun v => (localFact v).2.1⟩
  exact ⟨q,eq_of_beq rt,fun v => (localFact v).2.2.1,fun v => (localFact v).2.2.2⟩

set_option maxHeartbeats 3000000
theorem fixed_first (f : V → V) (inv : Function.Involutive f) (free : ∀ x,x≠f x)
    (other : ∀ x, first x≠f x) (atRoot : f root=target) (checked : allSecond=true) :
    ∃ (i : Fin 15) (q : Equiv.Perm V), q root=root ∧
      (∀ x, q (first x)=first (q x)) ∧ ∀ x, q (entry (canon i).2 x)=f (q x) := by
  have tm : f target=root := by rw [←atRoot,inv]
  have belongs (x : V) : x∈live ↔ x≠root ∧ x≠target := by simp [live]
  have stable (x) (mem : x∈live) : f x∈live := by
    obtain ⟨r,t⟩ := (belongs x).mp mem
    exact (belongs _).mpr ⟨fun e => t (inv.injective (e.trans tm.symm)), fun e => r (inv.injective (e.trans atRoot.symm))⟩
  obtain ⟨m,mem,res⟩ := enumerate_complete f inv free 16 live (by decide) (by decide) stable
  let edges := m.reverse++[(root,target)]
  have every : Respects f edges := by
    intro e he
    rcases List.mem_append.mp he with l|r
    · exact res _ (List.mem_reverse.mp l)
    · simp at r; subst e; exact atRoot
  have complete (v : V) : lookup edges v=f v := by
    apply lookup_agrees f inv edges every
    by_cases r : v=root
    · exact ⟨(root,target),by simp [edges],Or.inl r.symm⟩
    by_cases t : v=target
    · exact ⟨(root,target),by simp [edges],Or.inr t.symm⟩
    obtain ⟨u,hit⟩ := cover_node 16 live m mem v ((belongs v).mpr ⟨r,t⟩)
    rcases Bool.or_eq_true_iff.mp hit with d|d
    · exact ⟨(v,u),List.mem_append_left _ (List.mem_reverse.mpr (List.contains_iff_mem.mp d)),Or.inl rfl⟩
    · exact ⟨(u,v),List.mem_append_left _ (List.mem_reverse.mpr (List.contains_iff_mem.mp d)),Or.inr rfl⟩
  have can (e) (he : e∈m) : allow e.1 e.2=true := by
    have h := res e he
    simp [allow,← h,free,other]
  have yes := visit_sound allow checkPair 16 live [(root,target)] m mem can checked
  let tab := Vector.ofFn (lookup edges)
  let w := witness tab
  change validates tab w=true at yes
  obtain ⟨q,qr,qa,qb⟩ := witness_perm tab w yes
  refine ⟨w.kind,q,qr,qa,fun x => (qb x).trans ?_⟩
  exact (Vector.getElem_ofFn (f:=lookup edges) (q x).isLt).trans (complete (q x))

def pull (q : Equiv.Perm V) (f : V → V) (x : V) := q.symm (f (q x))
@[simp] theorem apply_pull (q : Equiv.Perm V) (f : V → V) (x : V) : q (pull q f x)=f (q x) := by simp [pull]
theorem pull_inv (q : Equiv.Perm V) {f : V → V} (inv : Function.Involutive f) :
    Function.Involutive (pull q f) := fun x => by simp [pull,inv (q x)]
theorem pull_free (q : Equiv.Perm V) {f : V → V} (free : ∀ x,x≠f x) (x : V) : x≠pull q f x :=
  fun e => free (q x) ((congrArg q e).trans (apply_pull ..))

set_option maxHeartbeats 1000000
theorem pair_normalization (a b : V → V) (ai : Function.Involutive a) (af : ∀ x,x≠a x)
    (bi : Function.Involutive b) (bf : ∀ x,x≠b x) (disjoint : ∀ x,a x≠b x)
    (checked : allSecond=true) :
    ∃ (i : Fin 15) (q : Equiv.Perm V), q root=root ∧ (∀ x,q (entry (canon i).1 x)=a (q x)) ∧
      ∀ x,q (entry (canon i).2 x)=b (q x) := by
  have fi : ∀ x,first (first x)=x := by native_decide
  have ff : ∀ x,x≠first x := by native_decide
  obtain ⟨p,pr,pa⟩ := RootedMatching.conjugate root first a fi ff ai af
  let d := pull p b
  have di := pull_inv p bi
  have df := pull_free p bf
  have diff (x) : first x≠d x := fun h => disjoint (p x) ((pa x).symm.trans ((congrArg p h).trans (apply_pull ..)))
  let z := d root
  let s := (moveToTarget z).symm
  have moves : ∀ u : V, u≠root → u≠first root → moveToTarget u root=root ∧ moveToTarget u u=target ∧
      ∀ x,moveToTarget u (first x)=first (moveToTarget u x) := by native_decide
  obtain ⟨mr,mz,mc⟩ := moves z (df root).symm (diff root).symm
  have sr : s root=root := (moveToTarget z).injective (by simpa [s] using mr.symm)
  have sc (x) : s (first x)=first (s x) := (moveToTarget z).injective (by simp [s,mc])
  let f := pull s d
  have fr : f root=target := by simpa [f,pull,sr,s] using mz
  have fo (x) : first x≠f x := fun h => diff (s x) ((sc x).symm ▸ (congrArg s h).trans (apply_pull ..))
  obtain ⟨i,q,qr,qa,qb⟩ := fixed_first f (pull_inv s di) (pull_free s df) fo fr checked
  have same : ∀ (j : Fin 15) (v : V), entry (canon j).1 v=first v := by native_decide
  refine ⟨i,(q.trans s).trans p,by simp [qr,sr,pr],?_,?_⟩
  · intro v; simp [same,qa,sc,pa]
  · intro v; simp [qb,f,d]

end WildExact.Seventeen
