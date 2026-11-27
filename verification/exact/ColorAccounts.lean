import PairAccount
import K17Pairs
import K17Numeric
import Moments

namespace WildExact.Seventeen
open WildExact Finset
set_option maxRecDepth 10000

noncomputable def partners (g : Coloring 17 17) (c : C) := mate (augment (by decide) g) c
noncomputable def kind (g : Coloring 17 17) (a b : C) := typeOf (partners g a) (partners g b)
noncomputable def adjustment (g : Coloring 17 17) (a b c : C) :=
  transfer (kind g a b) (kind g a c) (kind g b c)

private theorem refOne : ∀ (i : Fin 15) (x : V),refA.get x=entry (canon i).1 x := by native_decide
private theorem refTwo (i : Fin 15) (x : V) : (refB.get i).get x=entry (canon i).2 x := by
  simp [refB,Vector.get,Vector.getElem_ofFn]
private theorem refType (i : Fin 15) : typeOf refA.get (refB.get i).get=i := by
  have a : refA.get=first := funext (fun x => Vector.getElem_ofFn x.isLt)
  have b := funext (refTwo i)
  rw [a,b,type_canon]

def unused (i : Fin 15) (x : V) := univ.filter (fun y : V => x≠y ∧ refA.get x≠y ∧ (refB.get i).get x≠y)
def directed (i : Fin 15) : Int := ∑ x,∑ y∈unused i x,price i x y

theorem price_budget : ∀ i : Fin 15,directed i ≤20*(K17.data[i.val]!.both:Int)-2*3973540 := by native_decide
theorem transfer_budget : ∀ i j k : Fin 15,transfer i j k=transfer i k j ∧
    transfer i j k+transfer j i k+transfer k i j≤1 := by native_decide

private theorem distinct_mates (g : Coloring 17 17) {c d : C} (cd : c≠d) (x : V) : partners g c x≠partners g d x := by
  intro eq
  have h := (mate_spec (augment (by decide) g) c x).2
  change (augment (by decide) g).paint x (partners g c x)=c at h
  rw [eq] at h
  exact cd (h.symm.trans (mate_spec _ d x).2)

private theorem pay_sum (g : Coloring 17 17) (a b : C) (q : Equiv.Perm V) (i : Fin 15)
    (qa : ∀ x,q (refA.get x)=partners g a (q x))
    (qb : ∀ x,q ((refB.get i).get x)=partners g b (q x)) :
    (∑ c∈other a b,pay i (pull q (partners g c)))=directed i := by
  unfold pay directed
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  let h := augment (by decide) g
  let p := fun c => pull q (partners g c) x
  have inj : Function.Injective p := by
    intro c d eq
    by_contra ne
    exact distinct_mates g ne _ (by simpa [p] using congrArg q eq)
  have px (c) : x≠p c := pull_free q (fun v => (mate_spec h c v).1) x
  have pa : p a=refA.get x := q.injective ((apply_pull ..).trans (qa x).symm)
  have pb : p b=(refB.get i).get x := q.injective ((apply_pull ..).trans (qb x).symm)
  have cover : (other a b).image p=unused i x := by
    ext y
    simp only [unused,mem_filter,mem_univ,true_and,mem_image,other,mem_erase]
    constructor
    · rintro ⟨c,⟨cb,ca,_⟩,rfl⟩
      exact ⟨px c,pa ▸ fun eq => ca (inj eq).symm,pb ▸ fun eq => cb (inj eq).symm⟩
    · rintro ⟨xy,ay,by_⟩
      let c := h.paint (q x) (q y)
      have qxy : q x≠q y := fun eq => xy (q.injective eq)
      have py : p c=y := by
        apply q.injective
        rw [show q (p c)=partners g c (q x) from apply_pull ..]
        exact h.proper _ _ _ (mate_spec h c _).1 qxy (mate_spec h c _).2
      exact ⟨c,⟨fun eq => by apply by_; rw [←pb,←py,eq],fun eq => by apply ay; rw [←pa,←py,eq],True.intro⟩,py⟩
  rw [←cover,sum_image (fun _ _ _ _ eq => inj eq)]

private theorem lost_moves (q : Equiv.Perm V) (l t : Layout) (shape : ∀ x y,sameBlock t (q x) (q y)=sameBlock l x y)
    (f h : V → V) (maps : ∀ x,q (f x)=h (q x)) : lost h t=lost f l := by
  apply Bool.eq_iff_iff.mpr
  rw [lost_spec,lost_spec]
  exact (loss_transport q l t shape f h maps).symm

private theorem canonical_count (i : Fin 15) : pairScore refA.get (refB.get i).get=K17.data[i.val]!.both := by
  have ok := all_certified i
  simp only [certified,Bool.and_eq_true,beq_iff_eq] at ok
  exact (double_identity ..).symm.trans ok.1

/-- For an arbitrary ordered pair of colors, add the certified third-color inequalities. Every remaining edge contributes its price in both directions. -/
theorem accounts (g : Coloring 17 17) (a b : C) (ab : a≠b) :
    singleScore (partners g a)=8230880 ∧
    4*(∑ c∈other a b,(tripleScore (partners g a) (partners g b) (partners g c):Int)) ≤
      20*(pairScore (partners g a) (partners g b):Int)-2*3973540+
      2*∑ c∈other a b,adjustment g a b c := by
  obtain ⟨i,q,fixes,xa,xb⟩ := colors_normalize g a b ab
  have qa (x : V) : q (refA.get x)=partners g a (q x) := (congrArg q (refOne i x)).trans (xa x)
  have qb (x : V) : q ((refB.get i).get x)=partners g b (q x) := (congrArg q (refTwo i x)).trans (xb x)
  obtain ⟨e,shape⟩ := transport q fixes
  have la (l : Layout) := lost_moves q l (e l) (shape l) _ _ qa
  have lb (l : Layout) := lost_moves q l (e l) (shape l) _ _ qb
  have sc : singleScore refA.get=singleScore (partners g a) :=
    score_transport e _ _ (fun l => by simp only [la])
  have pc : pairScore refA.get (refB.get i).get=pairScore (partners g a) (partners g b) :=
    score_transport e _ _ (fun l => by simp only [shared,la,lb])
  constructor
  · exact sc.symm.trans ((single_identity _).symm.trans reference_single)
  have ij : kind g a b=i := (type_transport q fixes _ _ _ _ qa qb).symm.trans (refType i)
  have each (c : C) (hc : c∈other a b) :
      4*(tripleScore (partners g a) (partners g b) (partners g c):Int) ≤ pay i (pull q (partners g c))+2*adjustment g a b c := by
    obtain ⟨cb,ca,_⟩ := (show c≠b ∧ c≠a ∧ c∈univ from by simpa only [other,mem_erase] using hc)
    let f := pull q (partners g c)
    have move (x : V) : q (f x)=partners g c (q x) := apply_pull ..
    have tc : tripleScore refA.get (refB.get i).get f=tripleScore (partners g a) (partners g b) (partners g c) :=
      score_transport e _ _ (fun l => by simp only [shared,la,lb,lost_moves q l (e l) (shape l) _ _ move])
    have ta := type_transport q fixes _ _ _ _ qa move
    have tb := type_transport q fixes _ _ _ _ qb move
    have bound := canonical_triple i f (pull_inv q (mate_involutive _ c)) (pull_free q (fun x => (mate_spec _ c x).1))
      (fun x eq => distinct_mates g ca.symm _ ((qa x).symm.trans ((congrArg q eq).trans (move x))))
      (fun x eq => distinct_mates g cb.symm _ ((qb x).symm.trans ((congrArg q eq).trans (move x)))) (all_certified i)
    unfold adjustment
    rw [ij]
    simpa only [tc,ta,tb,kind] using bound
  have budget := sum_le_sum each
  rw [←mul_sum,sum_add_distrib,←mul_sum,pay_sum g a b q i qa qb] at budget
  have amount := price_budget i
  rw [←canonical_count,pc] at amount
  omega

end WildExact.Seventeen
