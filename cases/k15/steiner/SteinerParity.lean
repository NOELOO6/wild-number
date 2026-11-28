import Steiner15

namespace Wild15.Steiner.Parity
open WildExact WildDeletion WildSteiner Finset
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def parity (a : Fin 4 → Bool) := (a 0 != a 1) != (a 2 != a 3)

private theorem same_edge : ∀ a b c d : Bool,(a != b)=(c != d) → (a != c)=(b != d) := by decide

private theorem same_four : ∀ a b : Fin 4 → Bool,parity a=parity b →
    parity (fun i => a i != b i)=false := by decide

/-- A set of wild edges and a family of four-point parity constraints
admit a nonconstant simultaneous cut whenever their total rank is small. -/
theorem parity_cut {A I : Type} [Fintype A] [Fintype I] [DecidableEq A]
    (r : A) (W : Finset (A × A)) (Q : I → Fin 4 → A)
    (small : W.card+Fintype.card I+1<Fintype.card A) :
    ∃ t : A → Bool,t r=false ∧ (∃ x,t x=true) ∧
      (∀ e∈W,t e.1=t e.2) ∧ ∀ i,parity (fun j => t (Q i j))=false := by
  classical
  let sig (f : A → Bool) : (↥W → Bool) × (I → Bool) × Bool :=
    (fun e => f e.val.1 != f e.val.2, fun i => parity (fun j => f (Q i j)), f r)
  have size : Fintype.card ((↥W → Bool) × (I → Bool) × Bool)<Fintype.card (A → Bool) := by
    simpa [pow_add,mul_assoc] using (Nat.pow_lt_pow_right (by decide : 1<2) small)
  have collision : ∃ f g,f≠g ∧ sig f=sig g := by
    by_contra! no
    apply (Nat.not_le_of_lt size)
    exact Fintype.card_le_of_injective sig (fun {f g} eq => by_contra (fun ne => no f g ne eq))
  obtain ⟨f,g,ne,eq⟩ := collision
  have root := congrArg (fun p : (↥W → Bool) × (I → Bool) × Bool => p.2.2) eq
  change f r=g r at root
  refine ⟨fun x => f x != g x,by simp [root],?_,?_,?_⟩
  · by_contra! all
    apply ne
    funext x
    simpa using all x
  · intro e he
    exact same_edge _ _ _ _ (congrFun (congrArg Prod.fst eq) ⟨e,he⟩)
  · intro i
    exact same_four _ _ (congrFun (congrArg (fun p => p.2.1) eq) i)

def third (x y : V) : V := if x=y then x else Fin.ofNat' 15 (((x.val+1) ^^^ (y.val+1))-1)

def booleanSystem : System V where
  third := third
  same := by decide
  swap := by decide
  again := by decide

def original : Coloring 15 15 where
  paint := third
  symm := booleanSystem.swap
  proper := by decide +kernel

theorem is_steiner : SteinerColoring original := by
  have absent : ∀ x : V,Absent original x x := by
    change ∀ x y : V,x≠y → third x y≠x
    decide
  exact ⟨booleanSystem,fun x y _ => (unique_missing original (third x y)).choose_spec.2 _ (absent _)⟩

private def bucket (x : V) : Fin 4 := ⟨(x.val+1)/4,by omega⟩
private def digit (x : V) : Fin 4 := Fin.ofNat' 4 (x.val+1)
private def point (k i : Fin 4) : V := Fin.ofNat' 15 (4*k.val+i.val-1)
private def other (i : Fin 3) : Fin 4 := i.succ
private def shift (k : Fin 3) (c : V) : V := Equiv.swap 0 (k.castLE (by decide)) c

private theorem symmetric : ∀ (a b : Fin 3) (x y : V), (bucket x=bucket y → a=b) →
    shift a (third x y)=shift b (third y x) := by native_decide

/-- Independently exchange color zero with one of the three flexible
colors on each quartet and on the three-point line. -/
def redrawn (p : Fin 4 → Fin 3) : Coloring 15 15 where
  paint x y := shift (p (bucket x)) (third x y)
  symm x y := symmetric _ _ x y (congrArg p)
  proper _ _ _ xy xz h := original.proper _ _ _ xy xz ((Equiv.swap _ _).injective h)

def RedrawsThree (h : Coloring 15 15) := ∀ x y : V,x≠y →
  (if (original.paint x y).val<3 then (h.paint x y).val<3 else h.paint x y=original.paint x y)

private theorem allowed (p : Fin 4 → Fin 3) : RedrawsThree (redrawn p) := by
  have yes : ∀ (k : Fin 3) (c : V),if c.val<3 then (shift k c).val<3 else shift k c=c := by decide
  exact fun x y _ => yes _ _

private def localTest (triangle : Bool) (f : Fin 4 → Bool) (k : Fin 3) :=
  ∀ i j : Fin 4, (triangle=true → i≠0 ∧ j≠0) →
    (i.val ^^^ j.val)=k.val+1 → f i=f j

private theorem local_pair : ∀ (triangle : Bool) (f : Fin 4 → Bool),
    triangle=true ∨ parity f=false → ∃ k,localTest triangle f k := by
  unfold localTest
  native_decide

private theorem zeros : ∀ k : Fin 3,∀ x y : V,x≠y → shift k (third x y)=0 →
    bucket x=bucket y ∧ (digit x).val ^^^ (digit y).val=k.val+1 := by native_decide

private theorem recover_point : ∀ x : V,point (bucket x) (digit x)=x ∧ (bucket x=0 → digit x≠0) := by decide

/-- For this Steiner coloring every proposed set of ten wild edges
fails after some proper redraw of the same three colors. -/
theorem three_can_defeat (W : Lines 15) (small : W.card≤10) :
    ∃ h : Coloring 15 15,RedrawsThree h ∧ ¬Works h W := by
  classical
  obtain ⟨t,root,⟨x,hx⟩,flat,even⟩ := parity_cut (0 : V) W (fun i : Fin 3 => point (other i))
    (by simp only [Fintype.card_fin];omega)
  let f (b : Fin 4) (j : Fin 4) := t (point b j)
  have loc (b : Fin 4) : ∃ k,localTest (decide (b=0)) (f b) k := by
    apply local_pair
    refine Fin.cases (Or.inl (by decide)) (fun i => Or.inr (even i)) b
  choose p good using loc
  refine ⟨redrawn p,allowed p,fun win => ?_⟩
  have monochrome (u v : V) (ne : u≠v) (zero : (redrawn p).paint u v=0) : t u=t v := by
    obtain ⟨bucketEq,code⟩ := zeros _ u v ne zero
    have eq := good (bucket u) (digit u) (digit v) (fun h => ⟨(recover_point u).2 (of_decide_eq_true h),
      (recover_point v).2 (bucketEq ▸ of_decide_eq_true h)⟩) code
    simpa only [f,←bucketEq,(recover_point u).1] using eq.trans (congrArg t (bucketEq ▸ (recover_point v).1))
  have const {u v : V} (path : Walk (Joined (redrawn p) W 0) u v) : t u=t v := by
    induction path with
    | stay => rfl
    | step _ edge ih =>
      apply ih.trans
      rcases edge with (h|h)|⟨ne,col⟩
      · exact flat _ h
      · exact (flat _ h).symm
      · exact monochrome _ _ ne col
  have diff := const (win 0 0 x)
  simp [root,hx] at diff

private def groups : WildExact.Rotation.CutTest.Blocks 14 :=
  [[1,5,12],[7,8,9,11],[0,3,6,14],[2,4,10,13]]

private def wild : Lines 15 := (WildExact.Rotation.CutTest.drawing groups).toFinset

private theorem draws : Legal wild ∧ wild.card=11 := by
  constructor
  · change ∀ e∈wild,e.1<e.2
    decide
  · decide

private theorem three_options : ∀ c a b d : V,c.val<3 → a.val<3 → b.val<3 → d.val<3 →
    a≠b → a≠d → b≠d → a=c ∨ b=c ∨ d=c := by decide +kernel

open WildExact.Rotation.CutTest in
/-- Eleven edges suffice simultaneously for every proper redraw of
the three colors in this example. -/
theorem common_eleven : ∃ W : Lines 15,Legal W ∧ W.card=11 ∧
    ∀ h : Coloring 15 15,RedrawsThree h → Works h W := by
  classical
  let witness (s : List V) (x y : V) := s.contains x ≠ s.contains y
  have fixed : ∀ s∈cuts groups,∀ c : V,3≤c.val →
      ∃ x y : V,x≠y ∧ third x y=c ∧ witness s x y := by
    unfold witness
    native_decide
  have flex : ∀ s∈cuts groups,∃ x y z v : V,
      x≠y ∧ x≠z ∧ x≠v ∧ y≠z ∧ y≠v ∧ z≠v ∧
      (third x y).val<3 ∧ (third x z).val<3 ∧ (third x v).val<3 ∧
      witness s x y ∧ witness s x z ∧ witness s x v := by
    unfold witness
    native_decide
  refine ⟨wild,draws.1,draws.2,fun h redraw c => ?_⟩
  apply connected_of_crossings groups (by decide) (Joined h wild c) (joined_symm h)
  · intro B hB x y hx hy
    have path := block_walk groups B hB [] x y hx hy
    apply Walk.mapInto id _ path
    intro j k line
    rcases line with e|e
    · exact .step (.stay _) (Or.inl (Or.inl (List.mem_toFinset.mpr (by simpa using e))))
    · exact .step (.stay _) (Or.inl (Or.inr (List.mem_toFinset.mpr (by simpa using e))))
  · intro s hs
    have separated (x y : V) (h : witness s x y) : ¬(x∈s ↔ y∈s) :=
      fun same => h (Bool.eq_iff_iff.mpr (by simpa using same))
    by_cases k : c.val<3
    · obtain ⟨x,y,z,v,xy,xz,xv,yz,yv,zv,cy,cz,cv,dy,dz,dv⟩ := flex s hs
      have small (j : V) (ne : x≠j) (e : (third x j).val<3) : (h.paint x j).val<3 :=
        by simpa only [original,if_pos e] using redraw x j ne
      have q := three_options c _ _ _ k (small _ xy cy) (small _ xz cz) (small _ xv cv)
        (fun eq => yz (h.proper _ _ _ xy xz eq)) (fun eq => yv (h.proper _ _ _ xy xv eq))
        (fun eq => zv (h.proper _ _ _ xz xv eq))
      rcases q with eq|eq|eq
      · exact ⟨x,y,Or.inr ⟨xy,eq⟩,separated _ _ dy⟩
      · exact ⟨x,z,Or.inr ⟨xz,eq⟩,separated _ _ dz⟩
      · exact ⟨x,v,Or.inr ⟨xv,eq⟩,separated _ _ dv⟩
    · obtain ⟨x,y,ne,eq,sep⟩ := fixed s hs c (by omega)
      have hi : ¬(original.paint x y).val<3 := by change ¬(third x y).val<3;rw [eq];exact k
      exact ⟨x,y,Or.inr ⟨ne,(show h.paint x y=original.paint x y by simpa only [if_neg hi] using redraw x y ne).trans eq⟩,separated _ _ sep⟩

#print axioms common_eleven

#print axioms three_can_defeat
end Wild15.Steiner.Parity
