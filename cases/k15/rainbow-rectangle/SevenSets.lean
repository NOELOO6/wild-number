import Factors
namespace WildRectangle
set_option maxHeartbeats 3000000
open Finset
variable {V : Type} [DecidableEq V]

def Stable (p : V → V) (S : Finset V) := ∀ x,p x∈S ↔ x∈S

theorem Stable.inter {p : V → V} {S T : Finset V} (hs : Stable p S) (ht : Stable p T) : Stable p (S∩T) :=
  fun x => by simp only [mem_inter,hs x,ht x]

theorem Stable.union {p : V → V} {S T : Finset V} (hs : Stable p S) (ht : Stable p T) : Stable p (S∪T) :=
  fun x => by simp only [mem_union,hs x,ht x]

theorem Stable.sdiff {p : V → V} {S T : Finset V} (hs : Stable p S) (ht : Stable p T) : Stable p (S \ T) :=
  fun x => by simp only [mem_sdiff,hs x,ht x]

structure Seven (p : V → V) (U X : Finset V) : Prop where
  sub : X⊆U
  card : X.card=7
  stable : Stable p X
  long : ∀ x∈X,p (p x)≠x

private theorem atom (p : V → V) (inj : Function.Injective p) {U X D : Finset V} (q : Seven p U X)
    (sub : D⊆X) (st : Stable p D) : D.card=0 ∨ 3≤D.card := by
  by_cases no : D=∅
  · simp [no]
  obtain ⟨v,h⟩ := nonempty_iff_ne_empty.mpr no
  have ne := q.long v (sub h)
  have vp : v≠p v := by intro e; exact ne ((congrArg p e).symm.trans e.symm)
  have pp : p v≠p (p v) := fun e => vp (inj e)
  have sz : ({v,p v,p (p v)} : Finset V).card=3 := by simp [vp,ne.symm,pp]
  have pv := (st v).mpr h
  exact Or.inr (sz ▸ card_le_card (insert_subset h (insert_subset pv (singleton_subset_iff.mpr ((st _).mpr pv)))))

theorem seven_overlap {p : V → V} (inj : Function.Injective p) {U X Y : Finset V} (cap : U.card≤12)
    (x : Seven p U X) (y : Seven p U Y) (ne : X≠Y) : 3≤(X∩Y).card ∧ (X∩Y).card≤4 := by
  have a := atom p inj x inter_subset_left (x.stable.inter y.stable)
  have b := atom p inj x sdiff_subset (x.stable.sdiff y.stable)
  have unionSize := (card_le_card (union_subset x.sub y.sub)).trans cap
  have sum := card_union_add_card_inter X Y
  have part := card_sdiff_add_card_inter X Y
  have diff : (X \ Y).card≠0 := by
    intro e
    exact ne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp e)) (by rw [x.card,y.card]))
  rw [x.card,y.card] at sum
  rw [x.card] at part
  omega

/-- At most two seven-point unions of cycles can avoid both a fixed
point and its image when all cycles in those unions have length at least three. -/
theorem at_most_two {p : V → V} (inj : Function.Injective p) (U : Finset V) (cap : U.card≤12)
    (Q : Finset (Finset V)) (each : ∀ X∈Q,Seven p U X) : Q.card≤2 := by
  by_contra! bad
  obtain ⟨X,Y,Z,xq,yq,zq,xy,xz,yz⟩ := two_lt_card_iff.mp bad
  have x := each X xq
  have y := each Y yq
  have z := each Z zq
  have hx := seven_overlap inj cap x y xy
  have hy := seven_overlap inj cap y z yz
  have hz := seven_overlap inj cap x z xz
  let D := X∩Y∩Z
  have ds : Stable p D := (x.stable.inter y.stable).inter z.stable
  have d := atom p inj x (show D⊆X from inter_subset_left.trans inter_subset_left) ds
  have leftovers (A B : Finset V) (a : Seven p U A) (b : Seven p U B) (db : D⊆A∩B) :
      (A∩B).card=D.card ∨ 3+D.card≤(A∩B).card := by
    have eq := card_sdiff_add_card_eq_card db
    have h := atom p inj a (sdiff_subset.trans inter_subset_left) ((a.stable.inter b.stable).sdiff ds)
    omega
  have dxy : D⊆X∩Y := inter_subset_left
  have dxz : D⊆X∩Z := fun v hv => mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hv).1).1,(mem_inter.mp hv).2⟩
  have dyz : D⊆Y∩Z := fun v hv => mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hv).1).2,(mem_inter.mp hv).2⟩
  have ab := leftovers X Y x y dxy
  have ac := leftovers X Z x z dxz
  have bc := leftovers Y Z y z dyz
  have one (A B C : Finset V) (a : Seven p U A) (b : Seven p U B) (c : Seven p U C)
      (eq : (A∩B)∩(A∩C)=D) :
      A.card+D.card=(A∩B).card+(A∩C).card ∨ (A∩B).card+(A∩C).card+3≤A.card+D.card := by
    have h := atom p inj a (show A \ ((A∩B)∪(A∩C))⊆A from sdiff_subset) (a.stable.sdiff ((a.stable.inter b.stable).union (a.stable.inter c.stable)))
    have e := card_sdiff_add_card_eq_card (union_subset inter_subset_left inter_subset_left : (A∩B)∪(A∩C)⊆A)
    have e' := card_union_add_card_inter (A∩B) (A∩C)
    rw [eq] at e'
    omega
  have a0 := one X Y Z x y z (by ext v; simp [D]; tauto)
  have b0 := one Y X Z y x z (by ext v; simp [D]; tauto)
  have c0 := one Z X Y z x y (by ext v; simp [D]; tauto)
  rw [inter_comm Y X] at b0
  rw [inter_comm Z X,inter_comm Z Y] at c0
  have bound := (card_le_card (union_subset (union_subset x.sub y.sub) z.sub)).trans cap
  have e := card_union_add_card_inter (X∪Y) Z
  have f := card_union_add_card_inter X Y
  have g := card_union_add_card_inter (X∩Z) (Y∩Z)
  rw [show (X∪Y)∩Z=(X∩Z)∪(Y∩Z) by ext v; simp; tauto] at e
  rw [show (X∩Z)∩(Y∩Z)=D by ext v; simp [D]] at g
  rw [x.card] at a0
  rw [y.card] at b0
  rw [z.card] at c0 e
  rw [x.card,y.card] at f
  omega
end WildRectangle
