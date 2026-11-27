import LayoutTransport
import Counting
import Connectivity

namespace WildExact.Seventeen
open WildExact WildDeletion Finset

private def referenceSlots : List Slot := [13,12,12,12,12,12] ++ (List.finRange 12).map (fun i => Fin.ofNat' 14 i.val)

theorem layout_shape (l : Layout) : ((List.finRange 18).map (owner l)).Perm K17Connectivity.labels := by
  have big : ∀ b : Big, ((List.finRange 18).map (slot b)).Perm referenceSlots := by native_decide
  have small : ∀ p : Small, (referenceSlots.map (tag p)).Perm K17Connectivity.labels := by native_decide
  simpa only [List.map_map,Function.comp_def,owner] using ((big l.1).map (tag l.2)).trans (small l.2)

theorem alone (l : Layout) (x : V) : owner l x=0 ↔ x=root := by
  have big : ∀ (b : Big) (v : V), slot b v=13 ↔ v=root := by native_decide
  have small : ∀ (p : Small) (i : Slot), tag p i=0 ↔ i=13 := by native_decide
  exact (small _ _).trans (big _ _)

theorem ends_cover {n} (fuel : Nat) (xs : List (Fin (n+1))) (r : Row n)
    (h : r∈enumerate fuel xs) (nd : xs.Nodup) : (K17Connectivity.ends r).Perm xs := by
  induction fuel generalizing xs r with
  | zero => cases xs <;> simp [enumerate] at h
            subst r; rfl
  | succ k ih =>
    cases xs with
    | nil => simp [enumerate] at h; subst r; rfl
    | cons x xs =>
      obtain ⟨y,hy,t⟩ := List.mem_flatMap.mp h
      obtain ⟨r,mem,rfl⟩ := List.mem_map.mp t
      have uniq := (List.nodup_cons.mp nd).2
      have p := ih _ r mem (uniq.filter _)
      change (x::y::K17Connectivity.ends r).Perm (x::xs)
      apply List.Perm.cons
      rw [←uniq.erase_eq_filter y] at p
      exact (p.cons y).trans (List.perm_cons_erase hy).symm

def ordinaryPoint (x : V) : Fin 17 := Fin.ofNat' 17 x.val
theorem cast_ordinary {x : V} (notRoot : x≠root) : (ordinaryPoint x).castSucc=x := by
  have ne : x.val≠17 := fun e => notRoot (Fin.ext e)
  have lt := x.isLt
  exact Fin.ext (Nat.mod_eq_of_lt (by omega))

private theorem representatives (l : Layout) : ∃ rep : Block → V, ∀ i,owner l (rep i)=i := by
  have present : ∀ i : Block,i∈K17Connectivity.labels := by decide
  have all (i : Block) : ∃ x,owner l x=i := by
    obtain ⟨x,_,eq⟩ := List.mem_map.mp ((layout_shape l).mem_iff.mpr (present i))
    exact ⟨x,eq⟩
  exact Classical.axiomOfChoice all

private def lineFor (l : Layout) (rep : Block → V) (x : V) :=
  let a := ordinaryPoint x
  let b := ordinaryPoint (rep (owner l x))
  (min a b,max a b)

theorem winning_layout (g : Coloring 17 17) (l : Layout)
    (wins : ∀ c, ¬ Loss (mate (augment (by decide) g) c) l) : Upper g 12 := by
  classical
  obtain ⟨rep,section_⟩ := representatives l
  let centers := (univ : Finset Block).image rep
  let outer : Finset V := centersᶜ
  let w := outer.image (lineFor l rep)
  have inject : Function.Injective rep := fun {i j} eq => (section_ i).symm.trans ((congrArg (owner l) eq).trans (section_ j))
  have memOuter (x : V) : x∈outer ↔ x≠rep (owner l x) := by
    constructor
    · intro hx eq
      exact (Finset.mem_compl.mp hx) (eq ▸ Finset.mem_image_of_mem _ (mem_univ _))
    · intro ne
      apply Finset.mem_compl.mpr
      rintro mem
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mem
      exact ne (by rw [section_])
  have zero : rep 0=root := (alone _ _).mp (section_ 0)
  have both (x : V) (hx : x∈outer) : x≠root ∧ rep (owner l x)≠root := by
    have ne := (memOuter x).mp hx
    have o : owner l root=0 := (alone l root).mpr rfl
    have xr : x≠root := fun eq => ne (by rw [eq,o,zero])
    refine ⟨xr,fun eq => xr ((alone l x).mp ?_)⟩
    exact (section_ _).symm.trans ((congrArg (owner l) eq).trans o)
  have bound : outer.card=12 := by
    have h : centers.card=6 := by simp [centers,Finset.card_image_of_injective _ inject]
    simp [outer,Finset.card_compl,h]
  refine ⟨w,?_,(Finset.card_image_le.trans bound.le),?_⟩
  · intro e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hr,hs⟩ := both x hx
    have ne : ordinaryPoint x≠ordinaryPoint (rep (owner l x)) := fun eq =>
      (memOuter x).mp hx ((cast_ordinary hr).symm.trans ((congrArg Fin.castSucc eq).trans (cast_ordinary hs)))
    rcases lt_or_gt_of_ne ne with a|a <;> simp [lineFor,a,a.le]
  intro c
  let aug := augment (by decide) g
  let f := mate aug c
  let proj := fun x : V => if x=root then ordinaryPoint (f root) else ordinaryPoint x
  let E := fun x y : V => Walk (Joined g w c) (proj x) (proj y)
  have within (x : V) : E x (rep (owner l x)) := by
    by_cases eq : x=rep (owner l x)
    · rw [←eq]; exact .stay _
    have hx := (memOuter x).mpr eq
    obtain ⟨hr,hs⟩ := both x hx
    have drawn := Finset.mem_image_of_mem (lineFor l rep) hx
    apply Walk.step (.stay _)
    apply Or.inl
    simp only [proj,hr,hs,if_false]
    rcases le_total (ordinaryPoint x) (ordinaryPoint (rep (owner l x))) with h|h
    · exact Or.inl (by simpa only [w,lineFor,min_eq_left h,max_eq_right h] using drawn)
    · exact Or.inr (by simpa only [w,lineFor,min_eq_right h,max_eq_left h] using drawn)
  have colored (x : V) : E x (f x) := by
    have inv := mate_involutive aug c x
    have ne : x≠f x := (mate_spec aug c x).1
    by_cases hr : x=root
    · subst x; simp [E,proj,ne.symm,Walk.stay]
    by_cases fr : f x=root
    · have eq := (congrArg f fr).symm.trans inv
      simp [E,proj,hr,fr,eq,Walk.stay]
    apply Walk.step (.stay _)
    simp only [proj,hr,fr,if_false]
    apply Or.inr
    refine ⟨fun eq => ne ((cast_ordinary hr).symm.trans ((congrArg Fin.castSucc eq).trans (cast_ordinary fr))),?_⟩
    rw [←augment_paint (by decide),cast_ordinary hr,cast_ordinary fr]
    exact (mate_spec aug c x).2
  obtain ⟨rs,all⟩ := choose_rows aug
  let r := rs c
  have owned := (all c).2
  have cuts (keep : Block → Bool) (h : (K17Connectivity.blocks.filter keep).length=2) :
      ∃ e∈r, keep (owner l e.1) ≠ keep (owner l e.2) := by
    have two : ∀ p : Block → Bool, (K17Connectivity.blocks.filter p).length=2 →
        ∃ a b : Block,a≠b ∧ ∀ x,p x=((x==a)||(x==b)) := by native_decide
    obtain ⟨a,b,ab,keepEq⟩ := two keep h
    by_contra! no
    apply wins c
    refine ⟨rep a,rep b,by simp [sameBlock,section_,ab],fun x => ?_⟩
    have represents (z : V) : side l (rep a) (rep b) z = keep (owner l z) := by
      simp [side,sameBlock,section_,keepEq]
    rw [represents,represents]
    obtain ⟨y,hit⟩ := cover_node _ _ r (all c).1 x (List.mem_finRange x)
    rcases Bool.or_eq_true_iff.mp hit with hx|hx
    · have mem := List.contains_iff_mem.mp hx
      have eq := owned (x,y) mem
      exact eq.symm ▸ no (x,y) mem
    · have mem := List.contains_iff_mem.mp hx
      have eq := owned (y,x) mem
      have xy : f x=y := (congrArg f eq).symm.trans (mate_involutive aug c y)
      change keep (owner l x)=keep (owner l (f x))
      rw [xy]
      exact (no (y,x) mem).symm
  have connected := K17Connectivity.fifteen_cuts_suffice E (owner l) rep (layout_shape l)
    (fun x => ⟨.step (.stay _) (within x),.step (.stay _) (backwards (joined_symm g) (within x))⟩)
    r (ends_cover _ _ _ (all c).1 (List.nodup_finRange _))
    (fun e he => by
      have eq := owned e he
      have walk := colored e.1
      change f e.1=e.2 at eq
      rw [eq] at walk
      exact ⟨walk,backwards (joined_symm g) walk⟩) cuts
  intro x y
  have walk := Walk.mapInto proj (fun _ _ h => h) (connected x.castSucc y.castSucc)
  have pr (v : Fin 17) : proj v.castSucc=v := by
    have ne : v.castSucc≠root := Fin.ne_of_lt (Fin.castSucc_lt_last _)
    simp only [proj,ne,if_false]
    exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
  simpa only [pr] using walk

#print axioms winning_layout
end WildExact.Seventeen
