import SteinerSystems
import SteinerLayouts
import AlternatingLists

namespace Wild15.Steiner
open WildSteiner Finset Function WildAnchor WildAnchor.Alternating

private def slot (x : V) : Fin 3 ⊕ (Fin 6 × Bool) :=
  if h : x.val<3 then .inl ⟨x.val,h⟩ else
    .inr (⟨(x.val-3)/2,by have := x.isLt;omega⟩,decide ((x.val-3)%2=1))

private theorem slots : (∀ i,slot (left i)=.inr (i,false)) ∧
    (∀ i,slot (right i)=.inr (i,true)) := by decide

private theorem listed : (cycleLists 6 2 6).all lengths.contains=true ∧
    lengths.all (fun cs => (List.finRange 6).all fun i => (nextOf cs i).val==successor cs i.val)=true := by decide

/-- After choosing one line, the other pairs through its first two points
form two disjoint perfect matchings of the twelve remaining points. -/
theorem coordinates (S : System V) : ∃ (w : V ≃ V) (cs : List Nat),cs∈lengths ∧ w 0=0 ∧ w 1=1 ∧
    ∀ T∈seeds (nextOf cs),Genuine (S.reindex w) T := by
  classical
  let t := S.third 0 1
  have t0 : t≠0 := S.left_ne (by decide)
  have t1 : t≠1 := S.right_ne (by decide)
  let U : Finset V := {0,1,t}ᶜ
  have inside (x : V) : x∈U ↔ x≠0 ∧ x≠1 ∧ x≠t := by simp [U]
  have zeroClosed (x : ↥U) : S.third 0 x.val∈U := by
    obtain ⟨nz,no,nt⟩ := (inside _).mp x.property
    refine (inside _).mpr ⟨S.left_ne nz.symm,?_,?_⟩
    · intro h
      apply nt
      exact (S.again 0 x.val).symm.trans (congrArg (S.third 0) h)
    · intro h
      exact no ((S.again 0 x.val).symm.trans ((congrArg (S.third 0) h).trans (S.again 0 1)))
  have oneClosed (x : ↥U) : S.third 1 x.val∈U := by
    obtain ⟨nz,no,nt⟩ := (inside _).mp x.property
    refine (inside _).mpr ⟨?_,S.left_ne no.symm,?_⟩
    · intro h
      exact nt ((S.again 1 x.val).symm.trans ((congrArg (S.third 1) h).trans (S.swap 1 0)))
    · intro h
      exact nz ((S.again 1 x.val).symm.trans ((congrArg (S.third 1) h).trans (S.recover 0 1)))
  let P : Pairing ↥U := {
    first := fun x => ⟨S.third 0 x.val,zeroClosed x⟩
    second := fun x => ⟨S.third 1 x.val,oneClosed x⟩
    first_inv := fun x => Subtype.ext (S.again 0 x.val)
    second_inv := fun x => Subtype.ext (S.again 1 x.val)
    first_moves := fun x h => S.right_ne ((inside _).mp x.property).1.symm (congrArg Subtype.val h)
    second_moves := fun x h => S.right_ne ((inside _).mp x.property).2.1.symm (congrArg Subtype.val h) }
  have step (x : ↥U) : P.step x≠x := by
    intro h
    have eq : S.third 0 (S.third 1 x.val)=x.val := congrArg Subtype.val h
    have rev := (S.again 0 (S.third 1 x.val)).symm.trans (congrArg (S.third 0) eq)
    have same : S.third x.val 1=S.third x.val 0 := (S.swap _ _).trans (rev.trans (S.swap _ _))
    exact (by decide : (1 : V)≠0) ((S.again x.val 1).symm.trans ((congrArg (S.third x.val) same).trans (S.again x.val 0)))
  have low (x : ↥U) : 2≤P.period x := by
    have p := P.period_pos x
    have back : P.point x (P.period x)=x := iterate_minimalPeriod
    by_contra! no
    rw [show P.period x=1 by omega] at back
    exact step x back
  have size : Fintype.card ↥U=2*6 := by
    rw [Fintype.card_coe,show U={0,1,t}ᶜ from rfl,card_compl]
    simp [t0.symm,t1.symm]
  have non : 0<Fintype.card ↥U := by omega
  letI : Nonempty ↥U := Fintype.card_pos_iff.mp non
  obtain ⟨cs,ord,e,first,second⟩ := P.sorted_cycles size 2 low
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp listed.1 cs (cycle_member (by decide) ord))
  have perm (i : Fin 6) := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp listed.2 cs mem) i (List.mem_finRange i))
  let raw (x : V) : V := match slot x with
    | .inl i => if i=0 then 0 else if i=1 then 1 else t
    | .inr z => (e z).val
  have at0 : raw 0=0 := rfl
  have at1 : raw 1=1 := rfl
  have at2 : raw 2=t := rfl
  have atLeft (i) : raw (left i)=(e (i,false)).val := by simp [raw,slots.1]
  have atRight (i) : raw (right i)=(e (i,true)).val := by simp [raw,slots.2]
  have onto : Surjective raw := by
    intro x
    by_cases z : x=0
    · exact ⟨0,at0.trans z.symm⟩
    by_cases o : x=1
    · exact ⟨1,at1.trans o.symm⟩
    by_cases k : x=t
    · exact ⟨2,at2.trans k.symm⟩
    obtain ⟨⟨i,b⟩,hit⟩ := e.surjective ⟨x,(inside _).mpr ⟨z,o,k⟩⟩
    cases b
    · exact ⟨left i,(atLeft i).trans (congrArg Subtype.val hit)⟩
    · exact ⟨right i,(atRight i).trans (congrArg Subtype.val hit)⟩
  let w := Equiv.ofBijective raw ⟨Finite.injective_iff_surjective.mpr onto,onto⟩
  have line (a b c : V) (ne : a≠b) (h : S.third (raw a) (raw b)=raw c) :
      Genuine (S.reindex w) ⟨a,b,c⟩ := ⟨ne,w.symm_apply_eq.mpr h⟩
  refine ⟨w,cs,mem,at0,at1,fun T hT => ?_⟩
  have dis : ∀ i : Fin 6,(0 : V)≠left i ∧ (1 : V)≠left i := by decide
  change T∈([⟨0,1,2⟩] ++ ((List.finRange 6).map fun i => ⟨0,left i,right i⟩) ++
    (List.finRange 6).map fun i => ⟨1,left i,right (nextOf cs i)⟩) at hT
  rcases List.mem_append.mp hT with old|new
  · rcases List.mem_append.mp old with base|rest
    · obtain rfl := List.mem_singleton.mp base
      exact line _ _ _ (by decide) rfl
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp rest
      apply line _ _ _ (dis i).1
      rw [at0,atLeft,atRight]
      exact congrArg Subtype.val (first i)
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp new
    apply line _ _ _ (dis i).2
    rw [at1,atLeft,atRight]
    exact congrArg Subtype.val (second i _ (perm i))

/-- Put any two prescribed points at the first two positions of a seed. -/
theorem coordinates_at (S : System V) (u v : V) (ne : u≠v) :
    ∃ (w : V ≃ V) (cs : List Nat),cs∈lengths ∧ w 0=u ∧ w 1=v ∧
      ∀ T∈seeds (nextOf cs),Genuine (S.reindex w) T := by
  let a := Equiv.swap (0 : V) u
  have a0 : a 0=u := Equiv.swap_apply_left _ _
  have moving : a.symm v≠0 := fun h => ne (a0.symm.trans (a.symm_apply_eq.mp h).symm)
  let b := Equiv.swap (1 : V) (a.symm v)
  have b0 : b 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) moving.symm
  have b1 : b 1=a.symm v := Equiv.swap_apply_left _ _
  let p := b.trans a
  obtain ⟨e,cs,mem,e0,e1,start⟩ := coordinates (S.reindex p)
  refine ⟨e.trans p,cs,mem,?_,?_,start⟩
  · change a (b (e 0))=u
    rw [e0,b0,a0]
  · change a (b (e 1))=v
    rw [e1,b1,Equiv.apply_symm_apply]

end Wild15.Steiner
