import SixBoundary

namespace SixBoundary
open VertexRedraw EdgeWalk WildDeletion

theorem bit_lookup {α : Type} (p : α → Bool) (xs : List α) (i : Nat) :
    (bits p xs).testBit i = (xs[i]?.map p).getD false := by
  induction xs generalizing i with
  | nil => simp [bits]
  | cons x xs ih =>
    cases i with
    | zero => cases h : p x <;> simp [bits,h,Nat.testBit_shiftLeft]
    | succ i => cases h : p x <;> simp [bits,h,Nat.testBit_shiftLeft,ih,Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem positions_of_enough {s k : Nat} (h : enough k s=true) :
    ∃ is : List Nat, is.Nodup ∧ is.length=k ∧ ∀ i∈is,s.testBit i=true := by
  induction k generalizing s with
  | zero => exact ⟨[],by simp,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨nz,tail⟩ := Bool.and_eq_true_iff.mp h
    let t := s &&& (s-1)
    have sub (i) (hi : t.testBit i=true) : s.testBit i=true :=
      (Bool.and_eq_true_iff.mp (by simpa only [t,Nat.testBit_and] using hi)).1
    have diff : t ≠ s := by
      have small : t ≤ s-1 := Nat.and_le_right
      have pos : s≠0 := by simpa using nz
      omega
    have missing : ∃ i,s.testBit i=true ∧ t.testBit i=false := by
      apply Classical.byContradiction
      intro bad
      apply diff
      apply Nat.eq_of_testBit_eq
      intro i
      cases ht : t.testBit i with
      | true => exact (sub i ht).symm
      | false =>
        cases hs : s.testBit i with
        | true => exact False.elim (bad ⟨i,hs,ht⟩)
        | false => rfl
    obtain ⟨i,hi,notin⟩ := missing
    obtain ⟨ls,nd,len,ok⟩ := ih tail
    exact ⟨i::ls,List.nodup_cons.mpr ⟨fun mem => by have := ok i mem; simp_all [t],nd⟩,
      by simp [len],fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hi) (fun mem => sub _ (ok _ mem))⟩

def compatible (used : Nat) : List Row → Prop
  | [] => True
  | r::rs => used &&& r.hidden=0 ∧ compatible (used ||| r.hidden) rs
def remaining (alive : Nat) : List Row → Nat
  | [] => alive
  | r::rs => remaining (alive &&& r.wins) rs

private theorem zero_summands {α : Type} (f : α → Stats) (a : Stats) (xs : List α)
    (h : (xs.foldl (fun t x => t.add (f x)) a).belowNineteen=0) :
    a.belowNineteen=0 ∧ ∀ x ∈ xs,(f x).belowNineteen=0 := by
  induction xs generalizing a with
  | nil => exact ⟨h,by simp⟩
  | cons x xs ih =>
    obtain ⟨zero,more⟩ := ih _ h
    change a.belowNineteen + (f x).belowNineteen = 0 at zero
    exact ⟨by omega,fun y hy => (List.mem_cons.mp hy).elim (fun e => e ▸ (by omega)) (more _)⟩

inductive Choices : List Row → List (List Row) → Prop
  | nil : Choices [] []
  | cons {r opts rs bs} : r∈opts → Choices rs bs → Choices (r::rs) (opts::bs)

private theorem scan_branch (bs : List (List Row)) (rs : List Row) (used alive : Nat)
    (choices : Choices rs bs)
    (legal : compatible used rs) (h : (scan bs used alive).belowNineteen=0) :
    enough 19 (remaining alive rs) = true := by
  induction choices generalizing used alive with
  | nil =>
    simp only [scan] at h
    cases hx : enough 19 alive <;> simp_all [remaining]
  | @cons r opts rs bs hr _ ih =>
    let f (q : Row) := if used &&& q.hidden == 0 then scan bs (used ||| q.hidden) (alive &&& q.wins) else {}
    have sum : (opts.foldl (fun (t : Stats) x => t.add (f x)) {}).belowNineteen=0 := by
      have step (t : Stats) (q : Row) : t.add (f q) =
          (if used &&& q.hidden == 0 then t.add (scan bs (used ||| q.hidden) (alive &&& q.wins)) else t) := by
        split <;> simp_all [f,Stats.add]
      simpa only [step,scan] using h
    have chosen := (zero_summands f {} opts sum).2 r hr
    exact ih _ _ legal.2 (by simpa [f,legal.1] using chosen)

private theorem selectRows (f : C→V→V) (inv : ∀ c x,f c (f c x)=x)
    (ne : ∀ c x,f c x≠x) (agree : ∀ c x,x.val<6 → f c x=ref c x) (c : C) :
    ∃ m ∈ possible c,respects (f c) m := by
  have rinv : ∀ d x,ref d (ref d x)=x := by native_decide
  have full (x : V) (hx : held c x=true) : f c x=ref c x := by
    simp only [held,Bool.or_eq_true,decide_eq_true_eq] at hx
    rcases hx with left|right
    · exact agree c x left
    · have eq := agree c (ref c x) right
      rw [rinv] at eq
      exact (congrArg (f c) eq).symm.trans (inv c (ref c x))
  have closed : ∀ x∈free c,f c x∈free c := by
    intro x hx
    have no : held c x=false := by simpa [free] using (List.mem_filter.mp hx).2
    apply List.mem_filter.mpr
    refine ⟨(by decide : ∀ i : V,i∈points) _,?_⟩
    cases e : held c (f c x) with
    | false => rfl
    | true =>
      have eq := full _ e
      rw [inv] at eq
      have stable : ∀ d y,held d (ref d y)=held d y := by native_decide
      have contra := stable c (f c x)
      rw [←eq,no,e] at contra
      contradiction
  have len : ∀ d,(free d).length≤16 := by native_decide
  obtain ⟨m,hm,ok⟩ := fills_complete _ (inv c) (ne c) 16 _ (len c) closed
  refine ⟨knownPairs c++m,List.mem_map.mpr ⟨m,hm,rfl⟩,?_⟩
  intro e he
  rcases List.mem_append.mp he with old|new
  · obtain ⟨x,_,ev⟩ := List.mem_filterMap.mp old
    split at ev
    · cases ev
      apply full
      exact (Bool.and_eq_true_iff.mp (by assumption)).1
    · contradiction
  · exact ok _ new

private theorem hidden_disjoint {a b : V→V} {m n : R} (ia : ∀ x,a (a x)=x)
    (ib : ∀ x,b (b x)=x) (hm : respects a m) (hn : respects b n)
    (proper : ∀ x,a x≠b x) : (encode m).hidden &&& (encode n).hidden=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [encode,Nat.testBit_and,bit_lookup,Nat.zero_testBit]
  cases h : hiddenPairs[i]? with
  | none => simp
  | some e =>
    have get {v : V→V} {r : R} (iv : ∀ x,v (v x)=x) (allow : respects v r)
        (yes : (r.contains e || r.contains (e.2,e.1))=true) : v e.1=e.2 := by
      simp only [Bool.or_eq_true] at yes
      rcases yes with forward|back
      · exact allow _ (by simpa using forward)
      · have eq := allow _ (by simpa using back : (e.2,e.1)∈r)
        exact (congrArg v eq).symm.trans (iv e.2)
    change ((m.contains e || m.contains (e.2,e.1)) && (n.contains e || n.contains (e.2,e.1)))=false
    cases t : (m.contains e || m.contains (e.2,e.1)) with
    | false => rfl
    | true =>
      cases u : (n.contains e || n.contains (e.2,e.1)) with
      | false => rfl
      | true => exact False.elim (proper e.1 ((get ia hm t).trans (get ib hn u).symm))

private theorem and_or_disjoint {x y z : Nat} (hx : x &&& z=0) (hy : y &&& z=0) :
    (x ||| y) &&& z=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have a := congrArg (fun n : Nat => n.testBit i) hx
  have b := congrArg (fun n : Nat => n.testBit i) hy
  simp only [Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit] at *
  cases ex : x.testBit i <;> cases ey : y.testBit i <;> cases ez : z.testBit i <;> simp_all

private theorem compatible_of_pairwise (pick : C→Row) (cs : List C) (used : Nat)
    (nd : cs.Nodup) (prev : ∀ c∈cs,used &&& (pick c).hidden=0)
    (dis : ∀ c d,c≠d → (pick c).hidden &&& (pick d).hidden=0) :
    compatible used (cs.map pick) := by
  induction cs generalizing used with
  | nil => trivial
  | cons c cs ih =>
    obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp nd
    exact ⟨prev c (by simp),ih _ uniq (fun d hd => and_or_disjoint
      (prev d (by simp [hd])) (dis c d (fun eq => fresh (eq ▸ hd))))⟩

private theorem remaining_bit (rs : List Row) (alive i : Nat)
    (h : (remaining alive rs).testBit i=true) :
    alive.testBit i=true ∧ ∀ r∈rs,r.wins.testBit i=true := by
  induction rs generalizing alive with
  | nil => exact ⟨h,by simp⟩
  | cons r rs ih =>
    obtain ⟨both,more⟩ := ih _ h
    obtain ⟨head,good⟩ := Bool.and_eq_true_iff.mp (by simpa only [Nat.testBit_and] using both)
    exact ⟨head,fun x hx => (List.mem_cons.mp hx).elim (fun eq => eq ▸ good) (more _)⟩

/-- Each listed index gives its own grouping of the fixed six and the outside
nine. All fifteen ordinary graphs have paths after its ten wild edges are added. -/
theorem nineteen_of_census (verified : (scan (pools order) 0 initial).belowNineteen=0)
    (f : C→V→V) (inv : ∀ c x,f c (f c x)=x) (ne : ∀ c x,f c x≠x)
    (proper : ∀ c d,c≠d → ∀ x,f c x≠f d x)
    (agree : ∀ c x,x.val<6 → f c x=ref c x) :
    ∃ is : List Nat,is.Nodup ∧ is.length=19 ∧ ∀ i∈is,
      ∃ g, FixedSix.all[i]?=some g ∧ ∀ c,Connected (Adj (trial g++actualEdges (f c))) := by
  classical
  let m (c : C) := Classical.choose (selectRows f inv ne agree c)
  have spec (c : C) : m c∈possible c ∧ respects (f c) (m c) :=
    Classical.choose_spec (selectRows f inv ne agree c)
  let pick (c : C) := encode (m c)
  have choices (cs : List C) : Choices (cs.map pick)
      (cs.map fun c => (possible c).map encode) := by
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons (List.mem_map.mpr ⟨m c,(spec c).1,rfl⟩) ih
  have legal := compatible_of_pairwise pick order 0 (by decide) (by simp) (fun c d diff =>
    hidden_disjoint (inv c) (inv d) (spec c).2 (spec d).2 (proper c d diff))
  obtain ⟨is,nd,len,ok⟩ := positions_of_enough (scan_branch _ _ _ _ (choices order) legal verified)
  refine ⟨is,nd,len,?_⟩
  intro i hi
  have yes (c : C) := (remaining_bit _ _ i (ok i hi)).2 (pick c)
    (List.mem_map.mpr ⟨c,(by decide : ∀ d : C,d∈order) c,rfl⟩)
  have graph (c : C) : ((FixedSix.all[i]?).map (fun g => passes 0 (trial g ++ erase (m c)))).getD false = true := by
    simpa [pick,encode,bit_lookup,wilds,Function.comp_def] using yes c
  cases eq : FixedSix.all[i]? with
  | none => have := graph 0; simp [eq] at this
  | some g =>
    refine ⟨g,rfl,?_⟩
    intro c a b
    have h : passes 0 (trial g++erase (m c))=true := by simpa [eq] using graph c
    have sub {e} (mem : e∈trial g++erase (m c)) : e∈trial g++actualEdges (f c) := by
      rcases List.mem_append.mp mem with old|tail
      · exact List.mem_append_left _ old
      · obtain ⟨p,inc,image⟩ := List.mem_filterMap.mp tail
        apply List.mem_append_right
        apply List.mem_filterMap.mpr
        exact ⟨p,List.mem_map.mpr ⟨p.1,(by decide : ∀ x : V,x∈points) _,Prod.ext rfl ((spec c).2 p inc)⟩,image⟩
    exact Walk.mapInto id (fun _ _ edge => Walk.step (.stay _) (edge.imp sub sub))
      (connected_of_passes 0 _ h a b)
end SixBoundary
