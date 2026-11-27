import CommonHalf
import MatchingModel

namespace WildExact.Regroup
open Finset WildDeletion

private theorem even_of_pairing {V : Type} [Fintype V] [LinearOrder V]
    (f : V → V) (ff : Function.Involutive f) (moving : ∀ x, x ≠ f x) :
    Fintype.card V % 2 = 0 := by
  classical
  let side (x : V) := decide (x < f x)
  have h : Balanced (fun (_ : V) => ()) side := by
    refine ⟨⟨f,f,ff,ff⟩,fun x => ⟨rfl,?_⟩⟩
    change decide (f x < f (f x)) = !decide (x < f x)
    rw [ff x]
    rcases lt_or_gt_of_ne (moving x) with lt|gt
    · simp [lt,lt.asymm]
    · simp [gt,gt.asymm]
  have := h.count
  omega

/-- A component closed under the matching contains an even number of odd
blocks. The class labels may range over any type. -/
theorem even_block_count {V B A : Type} [LinearOrder V] [Fintype V] [Fintype B]
    [DecidableEq B] [DecidableEq A] (tag : V → B) (q : B → A)
    (odd : ∀ b, Fintype.card {v // tag v=b} % 2 = 1)
    (f : V → V) (ff : Function.Involutive f) (moving : ∀ x, x ≠ f x)
    (closed : ∀ v, q (tag (f v)) = q (tag v)) (a : A) :
    Fintype.card {b // q b=a} % 2 = 0 := by
  classical
  let X := {v // q (tag v)=a}
  let m : X → X := fun v => ⟨f v.val,(closed v.val).trans v.property⟩
  have parity : Fintype.card X % 2 = 0 := even_of_pairing m
    (fun v => Subtype.ext (ff v.val)) (fun v h => moving v.val (congrArg Subtype.val h))
  let spread : ((b : {b // q b=a}) × {v // tag v=b.val}) ≃ X :=
    { toFun := fun ⟨b,v⟩ => ⟨v.val,(congrArg q v.property).trans b.property⟩
      invFun := fun v => ⟨⟨tag v.val,v.property⟩,⟨v.val,rfl⟩⟩
      left_inv := by rintro ⟨⟨b,hb⟩,v,hv⟩; change tag v = b at hv; subst b; rfl
      right_inv := by intro v; rfl }
  rw [← Fintype.card_congr spread,Fintype.card_sigma,Finset.sum_nat_mod] at parity
  simpa only [odd,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using parity

/-- Inside each wild group any two points can reach each other. Outside the
groups the only moves supplied by this model are matching edges. -/
def GroupEdge {V B : Type} (tag : V → B) (f : V → V) (x y : V) : Prop :=
  tag x = tag y ∨ f x = y

def MergeEdge {V B : Type} (tag : V → B) (f : V → V) (side : B → Bool) (x y : V) : Prop :=
  GroupEdge tag f x y ∨ (side (tag x) = true ∧ side (tag y) = true)

private theorem group_symm {V B : Type} {tag : V → B} {f : V → V}
    (ff : Function.Involutive f) {x y} : GroupEdge tag f x y → GroupEdge tag f y x := by
  rintro (same|rfl)
  · exact Or.inl same.symm
  · exact Or.inr (ff x)

private def walks {V : Type} (E : V → V → Prop) (sym : ∀ {x y}, E x y → E y x) : Setoid V where
  r := Walk E
  iseqv := ⟨Walk.stay,backwards sym,Walk.join⟩

private def matchClass {V B : Type} (tag : V → B) (f : V → V) (ff : Function.Involutive f) :=
  walks (GroupEdge tag f) (group_symm ff)

private def blockClass {V B : Type} (tag : V → B) (rep : B → V)
    (f : V → V) (ff : Function.Involutive f) (b : B) : Quotient (matchClass tag f ff) :=
  Quotient.mk _ (rep b)

private theorem class_point {V B : Type} (tag : V → B) (rep : B → V)
    (hr : ∀ b, tag (rep b)=b) (f : V → V) (ff : Function.Involutive f) (v : V) :
    blockClass tag rep f ff (tag v) = Quotient.mk _ v :=
  Quotient.sound (show Walk (GroupEdge tag f) _ _ from .step (.stay _) (Or.inl (hr _)))

/-- Start with any partition into odd groups and any two perfect matchings.
Exactly half the groups can be merged, avoiding a prescribed group, so that
both matching graphs become connected. Previously connected matching graphs
stay connected under the same merge. -/
theorem two_color_merge {V B C : Type} [Fintype V] [LinearOrder V] [Fintype B] [DecidableEq B]
    (tag : V → B) (odd : ∀ b, Fintype.card {v // tag v=b} % 2 = 1)
    (partner : C → V → V) (invol : ∀ c, Function.Involutive (partner c))
    (moving : ∀ c v, v ≠ partner c v) (c d : C) (root : B) :
    ∃ side : B → Bool, side root = false ∧
      2 * (univ.filter (fun b => side b = true)).card = Fintype.card B ∧
      ∀ k, k=c ∨ k=d ∨ Connected (GroupEdge tag (partner k)) →
        Connected (MergeEdge tag (partner k) side) := by
  classical
  have present (b : B) : Nonempty {v // tag v=b} := by
    apply Fintype.card_pos_iff.mp
    have := odd b
    omega
  let rep (b : B) : V := (Classical.choice (present b)).val
  have hr (b : B) : tag (rep b)=b := (Classical.choice (present b)).property
  let q (k : C) := blockClass tag rep (partner k) (invol k)
  letI (k : C) : Fintype (Quotient (matchClass tag (partner k) (invol k))) := Fintype.ofFinite _
  have even (k) (a) : Fintype.card {b // q k b=a} % 2 = 0 := by
    apply even_block_count tag (q k) odd (partner k) (invol k) (moving k) _ a
    intro v
    apply (class_point tag rep hr _ (invol k) _).trans
    apply Eq.trans _ (class_point tag rep hr _ (invol k) _).symm
    exact Quotient.sound (show Walk (GroupEdge tag (partner k)) _ _ from
      .step (.stay _) (Or.inr (invol k v)))
  obtain ⟨side,hroot,hc,hd⟩ := common_bisection (q c) (q d) root (even c) (even d)
  refine ⟨side,hroot,hc.count,?_⟩
  intro k allow
  have lift {x y} (w : Walk (GroupEdge tag (partner k)) x y) :
      Walk (MergeEdge tag (partner k) side) x y :=
    Walk.mapInto (E := GroupEdge tag (partner k)) id (fun _ _ h => .step (.stay _) (Or.inl h)) w
  have balanced : Balanced (q k) side ∨ Connected (GroupEdge tag (partner k)) := by
    rcases allow with rfl|rfl|old
    · exact Or.inl hc
    · exact Or.inl hd
    · exact Or.inr old
  rcases balanced with h|old
  · have meet : ∀ x : V, ∃ y, side (tag y)=true ∧ Walk (GroupEdge tag (partner k)) x y := by
      intro x
      obtain ⟨b,eq,yes⟩ := h.hits (tag x)
      have qc := (class_point tag rep hr _ (invol k) x).symm.trans eq.symm
      exact ⟨rep b,by simpa [hr] using yes,Quotient.exact qc⟩
    intro x y
    obtain ⟨a,ha,xa⟩ := meet x
    obtain ⟨b,hb,yb⟩ := meet y
    exact ((lift xa).join (.step (.stay _) (Or.inr ⟨ha,hb⟩))).join
      (lift (backwards (group_symm (invol k)) yb))
  · exact fun x y => lift (old x y)

/-- The matching hypotheses of the merge theorem hold for every minimum
proper coloring on an even complete graph, including an augmented odd graph. -/
theorem coloring_merge {n : Nat} {B : Type} [Fintype B] [DecidableEq B]
    (g : Coloring (n+1) n) (tag : Fin (n+1) → B)
    (odd : ∀ b, Fintype.card {v // tag v=b} % 2 = 1) (c d : Fin n) (root : B) :
    ∃ side : B → Bool, side root = false ∧
      2 * (univ.filter (fun b => side b = true)).card = Fintype.card B ∧
      ∀ k, k=c ∨ k=d ∨ Connected (GroupEdge tag (mate g k)) →
        Connected (MergeEdge tag (mate g k) side) :=
  two_color_merge tag odd (mate g) (mate_involutive g) (fun k v => (mate_spec g k v).1) c d root

#print axioms coloring_merge
end WildExact.Regroup
