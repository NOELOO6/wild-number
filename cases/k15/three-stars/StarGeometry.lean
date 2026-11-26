import CutLedger
namespace ThreeStars
open VertexRedraw EdgeWalk WildDeletion

def tag (g : Layout) (v : Fin 15) : Group := Fin.ofNat' 5 (g.groups.findIdx (·.testBit v.val))
def hub (g : Layout) (i : Group) : Fin 15 :=
  ((List.finRange 15).find? (fun v => g.groups[i.val]!.testBit v.val)).getD 0
def invert (n : Fin 32) := ((List.range 5).filter n.val.testBit).length > 2
instance (n : Fin 32) : Decidable (invert n) := inferInstanceAs (Decidable (_ > _))
def pattern (n : Fin 32) (i : Group) := if invert n then !n.val.testBit i.val else n.val.testBit i.val
def choice (g : Layout) (n : Fin 32) := (List.finRange 5).foldl
  (fun s i => if pattern n i then s ||| g.groups[i.val]! else s) 0
def geometry (g : Layout) : Bool :=
  (List.finRange 15).all (fun v => (run (wild g) 15 (2^v.val)).testBit (hub g (tag g v)).val) &&
  (List.finRange 32).all fun n => n.val==0 || n.val==31 ||
    (let s := choice g n
     (ordSides g).contains s && decide (s<32768) &&
       (List.finRange 15).all (fun v => s.testBit v.val == pattern n (tag g v)))

private theorem encodable (p : Group → Bool) : ∃ n : Fin 32, ∀ i : Group, n.val.testBit i.val = p i := by
  have bits : ∀ a b c d e : Bool, ∃ n : Fin 32,
      n.val.testBit 0=a ∧ n.val.testBit 1=b ∧ n.val.testBit 2=c ∧ n.val.testBit 3=d ∧ n.val.testBit 4=e := by
    intro a b c d e
    refine ⟨Fin.ofNat' 32 (a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat + 16*e.toNat),?_⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  obtain ⟨n,h⟩ := bits (p 0) (p 1) (p 2) (p 3) (p 4)
  refine ⟨n,fun i => ?_⟩
  rcases (by decide : ∀ i : Group, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) i with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2

private theorem reversePath {n} {es : List (Edge n)} {a b : Fin n} (h : Walk (Adj es) a b) :
    Walk (Adj es) b a := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (E:=Adj es) (Walk.stay _) e.symm).join ih

private theorem oldPair (f : V → V) (x y : V) (eq : f x = y) (a : x.val<15) (b : y.val<15) :
    (⟨x.val,a⟩,⟨y.val,b⟩) ∈ actualEdges f := by
  apply List.mem_filterMap.mpr
  refine ⟨(x,y),List.mem_map.mpr ⟨x,(by decide : ∀ x : V,x∈points) x,Prod.ext rfl eq⟩,?_⟩
  simp [a,b]

private def extend (s : Nat) (r : V) := if s.testBit r.val then s ||| 32768 else s
private theorem old_bit (s : Nat) (r : V) (v : V) (h : v.val<15) :
    (extend s r).testBit v.val=s.testBit v.val := by
  have ne : 15 ≠ v.val := by omega
  have zero : (32768:Nat).testBit v.val=false := (by decide : ∀ i : Fin 15, (32768:Nat).testBit i.val=false) ⟨v.val,h⟩
  cases eq : s.testBit r.val <;> simp [extend,eq,show 32768=2^15 by decide,Nat.testBit_or,Nat.testBit_two_pow,ne,zero]
private theorem root_bit (s : Nat) (r : V) (h : s<32768) :
    (extend s r).testBit 15=s.testBit r.val := by
  have zero : s.testBit 15=false := Nat.testBit_lt_two_pow (i:=15) h
  cases e : s.testBit r.val <;> simp [extend,e,zero,Nat.testBit_or,show (32768:Nat).testBit 15=true by decide]

theorem path_of_unblocked (g : Layout) (good : geometry g=true) (m : R)
    (complete : full m=65535) (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x)
    (contains : respects f m) (clear : spoils g m=false) : Connected (Adj (wild g ++ actualEdges f)) := by
  classical
  let A := Adj (wild g ++ actualEdges f)
  intro x y
  apply Classical.byContradiction
  intro no
  let reach (v : Fin 15) := decide (Walk A x v)
  have invariant {a b : Fin 15} (path : Walk A a b) : reach a=reach b := by
    apply Bool.eq_iff_iff.mpr
    simp only [reach,decide_eq_true_eq]
    exact ⟨(·.join path),(·.join (reversePath path))⟩
  obtain ⟨paths,choices⟩ := Bool.and_eq_true_iff.mp good
  have inside (v : Fin 15) : reach v=reach (hub g (tag g v)) := by
    have hit := List.all_eq_true.mp paths v ((by decide : ∀ i : Fin 15, i∈List.finRange 15) v)
    apply invariant (Walk.mapInto id (E:=Adj (wild g)) _ (walk_of_seen v _ _ hit))
    intro i j h
    exact Walk.step (.stay _) (h.imp (List.mem_append_left _) (List.mem_append_left _))
  obtain ⟨n,label⟩ := encodable (fun i => reach (hub g i))
  have sameLabel (v : Fin 15) : n.val.testBit (tag g v).val=reach v := (label _).trans (inside v).symm
  have yes : reach x=true := by simp [reach,Walk.stay]
  have none : reach y=false := by simpa [reach,A] using no
  have nt : n.val ≠ 0 ∧ n.val ≠ 31 := by
    constructor
    · intro zero; have h := sameLabel x; simp [zero,yes] at h
    · intro full'; have h := sameLabel y
      have one : ∀ i : Group, (31:Nat).testBit i.val=true := by decide
      rw [full',one,none] at h; contradiction
  let s := choice g n
  have sel := List.all_eq_true.mp choices n ((by decide : ∀ i : Fin 32, i∈List.finRange 32) n)
  have hh : ((ordSides g).contains s && decide (s<32768)) &&
      (List.finRange 15).all (fun v => s.testBit v.val == pattern n (tag g v)) = true := by
    simpa [nt.1,nt.2,s] using sel
  obtain ⟨info,patt⟩ := Bool.and_eq_true_iff.mp hh
  obtain ⟨member,limit⟩ := Bool.and_eq_true_iff.mp info
  have small := of_decide_eq_true limit
  have pbit (v : Fin 15) : s.testBit v.val = if invert n then !(reach v) else reach v := by
    have bv := List.all_eq_true.mp (of_decide_eq_true patt) v ((by decide : ∀ i : Fin 15, i∈List.finRange 15) v)
    simpa [pattern,sameLabel] using bv
  let r := f 15
  have below : r.val<15 := by
    have hn := ne (15:V)
    have nz : r.val≠15 := fun e => hn (Fin.ext e)
    omega
  let z := extend s r
  have inSide : z ∈ sides g := by
    apply List.mem_flatMap.mpr
    refine ⟨s,List.contains_iff_mem.mp member,?_⟩
    cases h : s.testBit r.val <;> simp [z,extend,h]
  have sealed (e : Edge 16) (he : e∈m) : z.testBit e.1.val=z.testBit e.2.val := by
    have mate := contains e he
    by_cases lo : e.1.val<15
    · by_cases hi : e.2.val<15
      · have line := oldPair f e.1 e.2 mate lo hi
        have walk : Walk A (⟨e.1.val,lo⟩ : Fin 15) ⟨e.2.val,hi⟩ :=
          Walk.step (.stay _) (Or.inl (List.mem_append_right _ line))
        have same := invariant walk
        rw [old_bit s r _ lo,old_bit s r _ hi,pbit (⟨e.1.val,lo⟩ : Fin 15),pbit (⟨e.2.val,hi⟩ : Fin 15),same]
      · have hr : e.2=15 := Fin.ext (by have := e.2.isLt; omega)
        have back : e.1=r := by change e.1=f 15; rw [← hr,← mate]; exact (inv _).symm
        rw [hr,back,old_bit s r _ below]; exact (root_bit s r small).symm
    · have hr : e.1=15 := Fin.ext (by have := e.1.isLt; omega)
      have other : e.2=r := by simpa [hr,r] using mate.symm
      rw [hr,other,old_bit s r _ below]; exact root_bit s r small
  have short : z<65536 := by
    unfold z extend
    split
    · exact Nat.or_lt_two_pow (n:=16) (by omega) (by decide)
    · omega
  have hit : spoils g m=true := List.any_eq_true.mpr ⟨z,sealed_full short m complete sealed,List.contains_iff_mem.mpr inSide⟩
  simp [clear] at hit
end ThreeStars
