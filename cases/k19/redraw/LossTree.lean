import Std
namespace WildLoss

def tree (g : Nat → Nat) : List Nat → Nat → Nat
  | [],x => g x
  | a::l,x => tree g l x + tree g l (x+a)

theorem perm {xs ys : List Nat} (p : xs.Perm ys) (g : Nat → Nat) (x : Nat) :
    tree g xs x = tree g ys x := by
  induction p generalizing x with
  | nil => rfl
  | cons _ _ ih => simp only [tree,ih]
  | swap a b l =>
    simp only [tree]
    rw [show x+a+b=x+b+a by omega]
    omega
  | trans _ _ a b => exact (a x).trans (b x)

def score (g : Nat → Nat) (seeds weights : List Nat) := (seeds.map (tree g weights)).sum
def addPair (seeds : List Nat) (w : Nat) := seeds ++ seeds.map (·+w)

private theorem sum_pair (ss : List Nat) (f h : Nat → Nat) :
    (ss.map (fun x => f x+h x)).sum = (ss.map f).sum+(ss.map h).sum := by
  induction ss with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega
private theorem sum_append (xs ys : List Nat) : (xs++ys).sum = xs.sum+ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,Nat.add_assoc]
theorem expand (g : Nat → Nat) (seeds rest : List Nat) (w : Nat) :
    score g seeds (w::rest) = score g (addPair seeds w) rest := by
  simp only [score,addPair,List.map_append,sum_append,List.map_map,Function.comp_def]
  exact sum_pair _ _ _
theorem floor_score (g : Nat → Nat) (seeds rest : List Nat) :
    score g seeds [] ≤ score g seeds rest := by
  have h (x : Nat) (ws : List Nat) : g x ≤ tree g ws x := by
    induction ws generalizing x with
    | nil => exact Nat.le_refl _
    | cons a l ih => exact Nat.le_trans (ih x) (Nat.le_add_right _ _)
  induction seeds with
  | nil => exact Nat.le_refl _
  | cons a ss ih =>
    exact Nat.add_le_add (h a rest) ih

def ends {V : Type} (es : List (V×V)) := es.flatMap (fun e => [e.1,e.2])
def check {V : Type} [DecidableEq V] (g : Nat → Nat) (vkey : V → Nat) (target : Nat) :
    Nat → List V → List Nat → Bool
  | d,vs,ss =>
    if target ≤ score g ss [] then true else
    match d,vs with
    | k+1,a::left => left.all (fun b => check g vkey target k (left.erase b)
                         (addPair ss (vkey a+vkey b)))
    | _,_ => false

theorem check_sound {V : Type} [DecidableEq V] (g : Nat → Nat) (vkey : V → Nat) (target d : Nat)
    (vs : List V) (ss : List Nat) (es : List (V×V)) (hp : vs.Perm (ends es))
    (good : check g vkey target d vs ss = true) :
    target ≤ score g ss (es.map (fun e => vkey e.1+vkey e.2)) := by
  induction d generalizing vs ss es with
  | zero =>
    by_cases h : target ≤ score g ss []
    · exact Nat.le_trans h (floor_score _ _ _)
    · cases vs <;> simp [check,h] at good
  | succ d ih =>
    by_cases h : target ≤ score g ss []
    · exact Nat.le_trans h (floor_score _ _ _)
    cases vs with
    | nil => simp [check,h] at good
    | cons a rest =>
      have mem := hp.mem_iff.mp (List.mem_cons_self : a ∈ a::rest)
      obtain ⟨e,he,inside⟩ := List.mem_flatMap.mp mem
      let tail := @List.erase (V×V) instBEqOfDecidableEq es e
      have moved : es.Perm (e::tail) := by
        unfold tail
        apply List.perm_cons_erase
        exact he
      have ep := hp.trans (moved.flatMap_right (fun e : V×V => [e.1,e.2]))
      have step (b : V) (eq : e.1=a ∧ e.2=b ∨ e.2=a ∧ e.1=b) : target ≤
          score g ss (es.map (fun e => vkey e.1+vkey e.2)) := by
        have head : (a::rest).Perm (a::b::ends tail) := by
          change (a::rest).Perm (e.1::e.2::ends tail) at ep
          rcases eq with ⟨ha,hb⟩ | ⟨ha,hb⟩
          · simpa [ha,hb] using ep
          · simpa [ha,hb] using ep.trans (List.Perm.swap _ _ _)
        have hp2 := List.Perm.cons_inv head
        have hb : b ∈ rest := hp2.mem_iff.mpr List.mem_cons_self
        have hh := hp2.erase b
        simp only [List.erase_cons_head] at hh
        have next := List.all_eq_true.mp (show rest.all _ = true by simpa [check,h] using good) b hb
        have bound := ih (rest.erase b) (addPair ss (vkey a+vkey b)) tail hh next
        have p := moved.map (fun e => vkey e.1+vkey e.2)
        have peq : vkey e.1+vkey e.2=vkey a+vkey b := by rcases eq with ⟨aa,bb⟩|⟨aa,bb⟩ <;> simp [aa,bb,Nat.add_comm]
        have same : score g ss (es.map (fun e => vkey e.1+vkey e.2)) =
            score g ss ((vkey a+vkey b)::tail.map (fun e => vkey e.1+vkey e.2)) := by
          unfold score
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          simpa [peq] using perm p g x
        rw [same,expand]; exact bound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with first | second
      · exact step e.2 (Or.inl ⟨first.symm,rfl⟩)
      · exact step e.1 (Or.inr ⟨second.symm,rfl⟩)
end WildLoss
