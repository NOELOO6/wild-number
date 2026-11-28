import TripleRepair

namespace WildExact.TripleRepair
open Finset

variable {m : Nat} {V : Type} [Fintype V] [DecidableEq V]

private abbrev PairSlot := Slot × Slot
private def offset (s : Bool) : Slot := if s then 1 else 2

/-- A swapped row has two vertices on one side and one on the other.
Either choice of the first vertex on the double side names a different
cross-pair and its remaining forbidden completion. -/
private def localKey (p : PairSlot) (right pick : Bool) : PairSlot × (Bool × Slot) :=
  if right then ((p.1,p.2+offset pick),true,p.2+offset (!pick))
  else ((p.1+offset pick,p.2),false,p.1+offset (!pick))

private theorem local_key_unique : ∀ (p q : PairSlot) (r s i j : Bool),
    localKey p r i = localKey q s j → p=q ∧ r=s ∧ i=j := by decide

private def mixed (L : Layout m V) (a b : Fin m) (p : PairSlot) (right : Bool) : Finset V :=
  if right then {L (a,p.1),L (b,p.2+1),L (b,p.2+2)}
  else {L (a,p.1+1),L (b,p.2),L (a,p.1+2)}

private def site (L : Layout m V) (a b : Fin m) (q : Bool × Slot) : V :=
  L ((if q.1 then b else a),q.2)

omit [Fintype V] [DecidableEq V] in
private theorem site_inj (L : Layout m V) (a b : Fin m) (ab : a≠b) :
    Function.Injective (site L a b) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ eq
  obtain ⟨eq₁,eq₂⟩ := Prod.mk.inj (L.injective eq)
  cases r <;> cases s <;> simp_all [eq_comm]

omit [Fintype V] in
private theorem name_mixed (L : Layout m V) (a b : Fin m) (p : PairSlot) (r s : Bool) :
    let k := localKey p r s
    {L (a,k.1.1),L (b,k.1.2),site L a b k.2} = mixed L a b p r := by
  cases r <;> cases s <;> ext x <;> simp [localKey,mixed,site,offset,or_comm,or_left_comm,or_assoc]

/-- Either two swapped rows both pass, or three rows can be transposed so
that all three pass. Count forbidden completions over all nine cross-pairs. -/
private theorem alternatives (bad : Finset V → Prop) [DecidablePred bad]
    (d : Nat) (cap : ∀ x y : V, x≠y → (univ.filter fun z => bad {x,y,z}).card≤d)
    (large : d<m) (L : Layout m V) (a b : Fin m) (ab : a≠b) :
    (∃ p : PairSlot, ∀ r : Bool, ¬bad (mixed L a b p r)) ∨
    (∃ c : Fin m, c≠a ∧ c≠b ∧ ∃ s k : Slot, ∀ i : Slot,
      ¬bad {L (a,i),L (b,i+s),L (c,i+k)}) := by
  classical
  by_contra! no
  obtain ⟨sw,ex⟩ := no
  choose side hits using sw
  let rest := ((univ : Finset (Fin m)).erase a).erase b
  let External := ↥rest × (Slot × Slot)
  have blocked (p : External) : ∃ i : Slot,
      bad {L (a,i),L (b,i+p.2.1),L (p.1.val,i+p.2.2)} := by
    obtain ⟨cb,h⟩ := mem_erase.mp p.1.property
    exact ex _ (mem_erase.mp h).1 cb _ _
  choose idx fails using blocked
  let stop (q : PairSlot) := univ.filter fun z => bad {L (a,q.1),L (b,q.2),z}
  let Mark := (q : PairSlot) × ↥(stop q)
  let keyI (v : PairSlot × Bool) : Mark :=
    let k := localKey v.1 (side v.1) v.2
    ⟨k.1,site L a b k.2,mem_filter.mpr ⟨mem_univ _,by
      rw [show {L (a,k.1.1),L (b,k.1.2),site L a b k.2}=mixed L a b v.1 (side v.1) from
        name_mixed L a b v.1 _ v.2]
      exact hits _⟩⟩
  let keyE (p : External) : Mark :=
    ⟨(idx p,idx p+p.2.1),L (p.1.val,idx p+p.2.2),mem_filter.mpr ⟨mem_univ _,fails p⟩⟩
  have injI : Function.Injective keyI := by
    intro v w h
    have pair := congrArg Sigma.fst h
    have vert := congrArg (fun z : Mark => z.2.val) h
    have named := Prod.ext pair (site_inj L a b ab vert)
    obtain ⟨pq,_,ij⟩ := local_key_unique _ _ _ _ _ _ named
    exact Prod.ext pq ij
  have injE : Function.Injective keyE := by
    intro p q h
    have pair := congrArg Sigma.fst h
    have vert := congrArg (fun z : Mark => z.2.val) h
    change (idx p,idx p+p.2.1)=(idx q,idx q+q.2.1) at pair
    change L (p.1.val,idx p+p.2.2)=L (q.1.val,idx q+q.2.2) at vert
    obtain ⟨i,j⟩ := Prod.mk.inj pair
    rw [i] at j vert
    obtain ⟨r,k⟩ := Prod.mk.inj (L.injective vert)
    exact Prod.ext (Subtype.ext r) (Prod.ext (add_left_cancel j) (add_left_cancel k))
  have disjointKeys (v : PairSlot × Bool) (p : External) : keyI v ≠ keyE p := by
    intro h
    have vert := congrArg (fun z : Mark => z.2.val) h
    have eq := congrArg Prod.fst (L.injective vert)
    obtain ⟨cb,ha⟩ := mem_erase.mp p.1.property
    have ca := (mem_erase.mp ha).1
    change (if (localKey v.1 (side v.1) v.2).2.1 then b else a)=p.1.val at eq
    split at eq <;> simp_all
  let key : (PairSlot × Bool) ⊕ External → Mark := Sum.elim keyI keyE
  have inj : Function.Injective key := by
    rintro (v|p) (w|q) eq
    · exact congrArg Sum.inl (injI eq)
    · exact False.elim (disjointKeys v q eq)
    · exact False.elim (disjointKeys w p eq.symm)
    · exact congrArg Sum.inr (injE eq)
  have capacity := Fintype.card_le_of_injective key inj
  have per (q : PairSlot) : (stop q).card≤d :=
    cap _ _ (fun eq => ab (Prod.mk.inj (L.injective eq)).1)
  have K := sum_le_sum (s:=univ) (fun q _ => per q)
  have count : rest.card=m-1-1 := by simp [rest,card_erase_of_mem,ab.symm]
  simp [Mark,External,PairSlot,Slot,Fintype.card_sigma,count] at capacity K
  omega

private def row (L : Layout m V) (r : Fin m) : Finset V := {L (r,0),L (r,1),L (r,2)}

omit [Fintype V] in
private theorem row_from (L : Layout m V) (r : Fin m) (i : Slot) :
    row L r = {L (r,i),L (r,i+1),L (r,i+2)} := by
  rcases (show i=0 ∨ i=1 ∨ i=2 from (by decide : ∀ t : Slot, t=0 ∨ t=1 ∨ t=2) i) with rfl|rfl|rfl
  all_goals ext x; simp only [row,mem_insert,mem_singleton]
  · rfl
  · change _ ↔ x=L (r,1) ∨ x=L (r,2) ∨ x=L (r,0); tauto
  · change _ ↔ x=L (r,2) ∨ x=L (r,0) ∨ x=L (r,1); tauto

private def turn (s k : Slot) : Equiv.Perm (Slot × Slot) where
  toFun p := (p.2,p.1+(if p.2=1 then s else if p.2=2 then k else 0))
  invFun p := (p.2-(if p.1=1 then s else if p.1=2 then k else 0),p.1)
  left_inv := by rintro ⟨i,j⟩; simp
  right_inv := by rintro ⟨i,j⟩; simp

private def three (a b c : Fin m) (i : Slot) : Fin m := if i=0 then a else if i=1 then b else c

private theorem three_inj {a b c : Fin m} (ab : a≠b) (ca : c≠a) (cb : c≠b) :
    Function.Injective (three a b c) := by
  intro i j h
  have tri : ∀ t : Slot, t=0 ∨ t=1 ∨ t=2 := by decide
  rcases tri i with rfl|rfl|rfl <;> rcases tri j with rfl|rfl|rfl <;> simp_all [three,eq_comm]

/-- A forbidden family of unordered triples of pair degree at most d
admits a partition into m good triples whenever m>d and m≥2. -/
theorem partition_unordered (bad : Finset V → Prop) [DecidablePred bad]
    (d : Nat) (cap : ∀ x y : V, x≠y → (univ.filter fun z => bad {x,y,z}).card≤d)
    (large : d<m) (two : 2≤m) (start : Layout m V) :
    ∃ L : Layout m V, ∀ r, ¬bad {L (r,0),L (r,1),L (r,2)} := by
  classical
  let fails (L : Layout m V) := univ.filter fun r => bad (row L r)
  obtain ⟨L,_,least⟩ := exists_min_image (univ : Finset (Layout m V)) (fun L => (fails L).card)
    ⟨start,mem_univ _⟩
  refine ⟨L,fun a ha => ?_⟩
  have old : a∈fails L := mem_filter.mpr ⟨mem_univ _,ha⟩
  have improve (M : Layout m V) (S : Finset (Fin m)) (mem : a∈S)
      (pass : ∀ r∈S, ¬bad (row M r))
      (fixed : ∀ r∉S, ∀ j, M (r,j)=L (r,j)) : False := by
    have sub : fails M ⊆ (fails L).erase a := by
      intro r hr
      have hit := (mem_filter.mp hr).2
      have out : r∉S := fun h => pass r h hit
      exact mem_erase.mpr ⟨fun e => out (e ▸ mem),mem_filter.mpr ⟨mem_univ _,by
        simpa only [row,fixed r out] using hit⟩⟩
    exact (Nat.not_lt_of_ge (least M (mem_univ _)))
      ((card_le_card sub).trans_lt (card_lt_card (erase_ssubset old)))
  obtain ⟨b,ab⟩ : ∃ b : Fin m, a≠b := by
    let z : Fin m := ⟨0,by omega⟩
    by_cases h : a=z
    · exact ⟨⟨1,by omega⟩,by rw [h]; exact fun eq => Nat.zero_ne_one (congrArg Fin.val eq)⟩
    · exact ⟨z,h⟩
  rcases alternatives bad d cap large L a b ab with ⟨⟨i,j⟩,pass⟩|⟨c,ca,cb,s,k,pass⟩
  · let perm := Equiv.swap (a,i) (b,j)
    let M : Layout m V := perm.trans L
    have away (r : Fin m) (u : Slot) (ha : (r,u)≠(a,i)) (hb : (r,u)≠(b,j)) :
        M (r,u)=L (r,u) := congrArg L (Equiv.swap_apply_of_ne_of_ne ha hb)
    have other : ∀ t : Slot, t+1≠t ∧ t+2≠t := by decide
    have left (u : Slot) (ne : u≠i) : M (a,u)=L (a,u) :=
      away _ _ (fun h => ne (Prod.mk.inj h).2) (fun h => ab (Prod.mk.inj h).1)
    have right (u : Slot) (ne : u≠j) : M (b,u)=L (b,u) :=
      away _ _ (fun h => ab (Prod.mk.inj h).1.symm) (fun h => ne (Prod.mk.inj h).2)
    apply improve M {a,b} (by simp)
    · intro r hr
      rcases mem_insert.mp hr with er|hr
      · subst r
        have e : row M a=mixed L a b (i,j) false := by
          rw [row_from M a i,left _ (other i).1,left _ (other i).2]
          simp only [M,perm,Equiv.trans_apply,Equiv.swap_apply_left,mixed,Bool.false_eq_true,ite_false]
          ext x; simp [or_comm,or_left_comm,or_assoc]
        exact e ▸ pass false
      · obtain rfl := mem_singleton.mp hr
        have e : row M r=mixed L a r (i,j) true := by
          rw [row_from M r j,right _ (other j).1,right _ (other j).2]
          simp [M,perm,mixed]
        exact e ▸ pass true
    · intro r hr u
      simp only [mem_insert,mem_singleton,not_or] at hr
      exact away _ _ (fun h => hr.1 (Prod.mk.inj h).1) (fun h => hr.2 (Prod.mk.inj h).1)
  · let R := three a b c
    let emb : Slot × Slot ↪ Fin m × Slot :=
      (⟨R,three_inj ab ca cb⟩ : Slot ↪ Fin m).prodMap (Function.Embedding.refl Slot)
    let M : Layout m V := ((turn s k).viaEmbedding emb).trans L
    apply improve M (univ.image R) (mem_image.mpr ⟨0,mem_univ _,rfl⟩)
    · intro r hr
      obtain ⟨i,_,rfl⟩ := mem_image.mp hr
      have mv (j : Slot) : M (R i,j)=L (emb (turn s k (i,j))) := by
        change L ((turn s k).viaEmbedding emb (emb (i,j)))=_
        rw [Equiv.Perm.viaEmbedding_apply]
      simp only [row,mv]
      simpa [emb,turn,R,three] using pass i
    · intro r hr j
      change L ((turn s k).viaEmbedding emb (r,j))=_
      rw [Equiv.Perm.viaEmbedding_apply_of_not_mem]
      rintro ⟨⟨i,u⟩,eq⟩
      exact hr (mem_image.mpr ⟨i,mem_univ _,congrArg Prod.fst eq⟩)

#print axioms partition_unordered
end WildExact.TripleRepair
