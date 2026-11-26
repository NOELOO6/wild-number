import RedrawModel
import BoundaryProof
namespace RedrawModel
open VertexRedraw EdgeWalk WildDeletion Std.Sat
set_option maxRecDepth 6000

def assignment (pick : C → Nat) (i : Nat) :=
  (info i).2.testBit (pick (info i).1)
private theorem one_bit (c : C) (j) (h : j < (opts c).size) : (ones c).testBit j=true := by
  simpa only [ones,Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using h

private theorem supported (pick : C→Nat) (inBounds : ∀ c, pick c < (opts c).size)
    (c : C) (cl : Clause) (h : (supports c cl).testBit (pick c)=true) :
    cl.eval (assignment pick) = true := by
  induction cl with
  | nil => simp [supports] at h
  | cons l tail ih =>
    rcases l with ⟨v,pos⟩
    have b := one_bit _ _ (inBounds c)
    obtain ⟨d,s,eq⟩ : ∃ d s, info v=(d,s) := ⟨_,_,rfl⟩
    simp only [supports,eq,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with head|rest
    · by_cases same : c=d
      · subst d
        cases pos <;> cases hv : s.testBit (pick c) <;>
          simp_all [CNF.Clause.eval_cons,assignment,Nat.testBit_xor]
      · simp [same] at head
    · simp [CNF.Clause.eval_cons,ih rest]

private theorem row_bit (p : R → Bool) (c : C) (j : Nat) (h : j < (opts c).size) :
    (onRows c p).testBit j=p (row c j) := by
  simp [onRows,SixBoundary.bit_lookup,row,Array.getElem?_eq_getElem h]

private theorem andBit {s t i : Nat} (eq : s &&& t=t) (h : t.testBit i=true) : s.testBit i=true := by
  have it := congrArg (fun x : Nat => x.testBit i) eq
  simpa [Nat.testBit_and,h] using it

private theorem orBit {s t all i : Nat} (eq : (s ||| t) &&& all=all) (h : all.testBit i=true)
    (no : s.testBit i=false) : t.testBit i=true := by
  have it := congrArg (fun x : Nat => x.testBit i) eq
  simpa [Nat.testBit_and,Nat.testBit_or,h,no] using it

private theorem mate {f : V→V} {m : R} (inv : ∀ x, f (f x)=x) (res : respects f m)
    (x y) (h : hasEdge m x y=true) : f x=y := by
  simp only [hasEdge,Bool.or_eq_true,List.contains_iff_mem] at h
  exact h.elim (res _) (fun q => (congrArg f (res _ q)).symm.trans (inv y))

private theorem liftRow {f : V→V} {m : R} (res : respects f m) (g : List Nat)
    (yes : passes 0 (trial g++erase m)=true) : Connected (Adj (trial g++actualEdges f)) := by
  have sub {e} (mem : e∈trial g++erase m) : e∈trial g++actualEdges f := by
    rcases List.mem_append.mp mem with old|tail
    · exact List.mem_append_left _ old
    · obtain ⟨p,inc,image⟩ := List.mem_filterMap.mp tail
      apply List.mem_append_right
      apply List.mem_filterMap.mpr
      exact ⟨p,List.mem_map.mpr ⟨p.1,(by decide : ∀ x : V,x∈points) _,Prod.ext rfl (res p inc)⟩,image⟩
  intro a b
  exact Walk.mapInto id (fun _ _ edge => Walk.step (.stay _) (edge.imp sub sub)) (connected_of_passes 0 _ yes a b)

def Wins (f : C→V→V) := ∃ g ∈ FixedSix.all, (trial g).length=10 ∧ (trial g).Nodup ∧
  ∀ c, Connected (Adj (trial g++actualEdges (f c)))

structure Checks : Prop where
  endorsed : census=true
  lengths : tags.size=formula.length
  edges : ∀ c x y, em c x y=eMask c x y
  wins : ∀ i, i<groups.size → ∀ c, wm i c=wMask c groups[i]!
  groupsOK : ∀ i, i<groups.size → groups[i]!∈FixedSix.all ∧
    (trial groups[i]!).length=10 ∧ (trial groups[i]!).Nodup
  rowsOK : ∀ c j, j<(opts c).size → ∀ x, ∃ y, hasEdge (row c j) x y=true

private theorem holds (chk : Checks) (f : C→V→V) (inv : ∀ c x, f c (f c x)=x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x) (cover : ∀ x y : V, x≠y → ∃ c, f c x=y)
    (pick : C→Nat) (hb : ∀ c, pick c < (opts c).size)
    (res : ∀ c, respects (f c) (row c (pick c))) (noWin : ¬Wins f)
    (cl : Clause) (tag : List Nat) (cert : valid cl tag=true) : cl.eval (assignment pick)=true := by
  apply Classical.byContradiction
  intro bad
  have no (c : C) : (supports c cl).testBit (pick c)=false := by
    cases flag : (supports c cl).testBit (pick c) with
    | false => rfl
    | true => exact False.elim (bad (supported pick hb c cl flag))
  have emBit (c : C) (x y : V) : (em c x y).testBit (pick c)=hasEdge (row c (pick c)) x y :=
    (congrArg (fun n : Nat => n.testBit (pick c)) (chk.edges c x y)).trans (row_bit _ _ _ (hb c))
  have cmem : ∀ c : C, c∈colors := by decide
  unfold valid at cert
  split at cert
  next d =>
    let c := Fin.ofNat' 15 d
    have yes := andBit (beq_iff_eq.mp cert : supports c cl &&& ones c=ones c) (one_bit c _ (hb c))
    exact bad (supported _ hb c _ yes)
  next a b =>
    obtain ⟨diff,checks⟩ := Bool.and_eq_true_iff.mp cert
    let x := Fin.ofNat' 16 a
    let y := Fin.ofNat' 16 b
    obtain ⟨c,fc⟩ := cover x y (by simpa using diff)
    obtain ⟨z,hz⟩ := chk.rowsOK c _ (hb c) x
    have same := (mate (inv c) (res c) _ _ hz).symm.trans fc
    subst z
    have yes := andBit (beq_iff_eq.mp (List.all_eq_true.mp checks c (cmem c))) ((emBit c x y).trans hz)
    exact bad (supported _ hb c _ yes)
  next a b d h =>
    obtain ⟨diff,checks⟩ := Bool.and_eq_true_iff.mp cert
    let x := Fin.ofNat' 16 a
    let y := Fin.ofNat' 16 b
    let c := Fin.ofNat' 15 d
    let k := Fin.ofNat' 15 h
    have forced (j) (mem : j∈[c,k]) : f j x=y := by
      have hb' := orBit (beq_iff_eq.mp (List.all_eq_true.mp checks j mem)) (one_bit j _ (hb j)) (no j)
      exact mate (inv j) (res j) _ _ ((emBit j x y).symm.trans hb')
    exact proper c k (by simpa using diff) x ((forced c (by simp)).trans (forced k (by simp)).symm)
  next i =>
    obtain ⟨lt,checks⟩ := Bool.and_eq_true_iff.mp cert
    have hi : i<groups.size := of_decide_eq_true lt
    obtain ⟨legal,size,distinct⟩ := chk.groupsOK i hi
    apply noWin
    refine ⟨_,legal,size,distinct,?_⟩
    intro c
    have bit := orBit (beq_iff_eq.mp (List.all_eq_true.mp checks c (cmem c))) (one_bit c _ (hb c)) (no c)
    rw [chk.wins _ hi] at bit
    exact liftRow (res c) _ ((row_bit _ _ _ (hb c)).symm.trans bit)
  next => contradiction

private theorem tagged {α β} (xs : List α) (ys : List β) (len : xs.length=ys.length) (a : α)
    (mem : a∈xs) : ∃ b,(a,b)∈xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at mem
  | cons x xs ih =>
    cases ys with
    | nil => simp at len
    | cons y ys =>
      rcases List.mem_cons.mp mem with rfl|tail
      · exact ⟨y,List.mem_cons_self⟩
      · obtain ⟨b,hb⟩ := ih _ (by simpa using len) tail
        exact ⟨b,List.mem_cons_of_mem _ hb⟩

theorem redraw_wins (chk : Checks) (unsat : formula.Unsat)
    (f : C→V→V) (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (cover : ∀ x y : V, x≠y → ∃ c, f c x=y)
    (agree : ∀ c x, BoundaryOptions.fixedAt lock c x=true → f c x=SixBoundary.ref c x) : Wins f := by
  classical
  apply Classical.byContradiction
  intro noWin
  have sel (c) : ∃ j, j<(opts c).size ∧ respects (f c) (row c j) := by
    obtain ⟨m,mem,ok⟩ := BoundaryOptions.represented lock (by native_decide) f inv ne proper agree c
    have same : ∀ d, (opts d).toList=BoundaryOptions.possible lock d := by native_decide
    rw [← same] at mem
    obtain ⟨j,hj,hit⟩ := List.getElem_of_mem mem
    refine ⟨j,by simpa using hj,?_⟩
    have jlt : j<(opts c).size := by simpa using hj
    simpa [row,Array.getElem?_eq_getElem jlt,←hit] using ok
  let pick c := Classical.choose (sel c)
  have spec c := Classical.choose_spec (sel c)
  have feasible : formula.eval (assignment pick)=true := by
    apply List.all_eq_true.mpr
    intro cl mem
    obtain ⟨tag,member⟩ := tagged _ tags.toList (by simpa using chk.lengths.symm) _ mem
    exact holds chk f inv proper cover pick (fun c => (spec c).1) (fun c => (spec c).2) noWin _ _
      (List.all_eq_true.mp chk.endorsed _ member)
  rw [unsat] at feasible
  contradiction
end RedrawModel
