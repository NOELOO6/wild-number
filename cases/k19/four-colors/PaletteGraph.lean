import PaletteChecks
import GraphSieve
namespace WildPalette
open Finset WildSieve WildDeletion WildExact
set_option maxHeartbeats 1000000

/-- Agreement of every unchanged color, including its edge at the extra root. -/
def Fixed (g : Coloring 20 19) (P : Finset C) := ∀ c,c∉P → ∀ v,mate g c v=partner c v

private theorem original_covers : ∀ x y : V,x≠y → ∃ c,partner c x=y := by native_decide
private theorem allowed (g : Coloring 20 19) (P : Finset C) (fixed : Fixed g P) (c : C) (hc : c∈P) (x : V) :
    ∃ d∈P,mate g c x=partner d x := by
  obtain ⟨d,eq⟩ := original_covers x _ (mate_spec g c x).1
  refine ⟨d,?_,eq.symm⟩
  by_contra notIn
  have m := (fixed d notIn x).trans eq
  have cd := (coloringFactor g).unique x m
  exact notIn (cd.symm ▸ hc)

def lines (r : Nat) : Lines 19 := univ.biUnion (fun j : Fin 6 => spokes (oldPart (region r j.castSucc)))

private theorem outside_root (r : Nat) (reg : regular r) (j : Fin 6) : Fin.last 19∉region r j.castSucc := by
  intro h
  have atRoot : Fin.last 19∈region r 6 := reg.1 ▸ mem_singleton_self _
  exact Fin.castSucc_ne_last j ((mem_filter.mp h).2.symm.trans (mem_filter.mp atRoot).2)

private theorem size_lines (r : Nat) (reg : regular r) : Legal (lines r) ∧ (lines r).card≤13 := by
  constructor
  · intro e he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    exact spokes_legal _ _ hj
  · apply card_biUnion_le.trans
    calc
      _≤∑ j : Fin 6,((if j=0 then 4 else 3)-1 : Nat) := sum_le_sum (fun j _ =>
          (spokes_bound _).trans (by rw [old_size _ (outside_root r reg j),reg.2 j]))
      _=13 := by decide

private theorem size_eq (r : Nat) (s : Cut) (Q : Finset V) (bits : ∀ x,bit r s x=decide (x∈Q)) :
    size r s=Q.card := by
  let l := (List.finRange 20).filter (bit r s)
  have nd := (List.nodup_finRange 20).filter (bit r s)
  have eq : l.toFinset=Q := by
    ext x;simp [l,bits]
  exact (List.toFinset_card_of_nodup nd).symm.trans (congrArg card eq)

private theorem no_side (r : Nat) (P : Finset C) (reg : regular r) (orig : original r) (share : shared r P)
    (F : Coloring 20 19) (fix : Fixed F P) (c : C) (Q : Finset V)
    (pos : Q.Nonempty) (neg : Qᶜ.Nonempty) (out : Fin.last 19∉Q)
    (cl : Closed (mate F c) Q) (whole : ∀ j : G,Cohesive (region r j) Q) : False := by
  classical
  let f (j : G) := decide ((region r j∩Q).Nonempty)
  have blank : ({Fin.last 19}:Finset V)∩Q=∅ := disjoint_iff_inter_eq_empty.mp (disjoint_singleton_left.mpr out)
  have f6 : f 6=false := by simp only [f,reg.1,blank,Finset.not_nonempty_empty,decide_false]
  obtain ⟨s,fs⟩ := mask_exists f f6
  have bits (x : V) : bit r s x=decide (x∈Q) := by
    rw [bit,fs]
    apply Bool.eq_iff_iff.mpr
    simp only [f,decide_eq_true_eq]
    have own : x∈region r (group r x) := mem_filter.mpr ⟨mem_univ _,rfl⟩
    constructor
    · rintro ⟨y,hy⟩
      exact whole _ y (mem_inter.mp hy).1 x own (mem_inter.mp hy).2
    · exact fun h => ⟨x,mem_inter.mpr ⟨own,h⟩⟩
  have yes : tested r s := by
    have p := card_pos.mpr pos
    have q := card_pos.mpr neg
    rw [card_compl,Fintype.card_fin] at q
    have sz := closed_size (mate_involutive F c) (fun x => (mate_spec F c x).1) cl
    unfold tested
    rw [size_eq r s Q bits]
    omega
  have same (x) : bit r s x=bit r s (mate F c x) := by
    simp only [bits]
    apply Bool.eq_iff_iff.mpr
    simp only [f,decide_eq_true_eq]
    exact ⟨cl x,fun h => mate_involutive F c x ▸ cl _ h⟩
  by_cases h : c∈P
  · obtain ⟨x,cross⟩ := share s yes
    obtain ⟨d,hd,eq⟩ := allowed F P fix c h x
    exact cross d hd (eq ▸ same x)
  · obtain ⟨x,cut⟩ := orig s yes c
    exact cut (fix c h x ▸ same x)

private theorem paths (r : Nat) (P : Finset C) (reg : regular r) (orig : original r) (share : shared r P)
    (g : Coloring 19 19) (fixed : Fixed (augment (by decide) g) P) : Works g (lines r) := by
  classical
  intro c x y
  apply Classical.byContradiction
  intro lost
  obtain ⟨S,left,⟨v,nv⟩,cl,wh⟩ := closed_side_of_failure g (by decide) (lines r) c x y lost
  let F := augment (by decide) g
  have whole (j : G) : Cohesive (region r j) S := by
    cases j using Fin.lastCases with
    | last =>
      change Cohesive (region r (6 : G)) S
      rw [reg.1]
      intro a ha b hb
      rw [mem_singleton.mp ha,mem_singleton.mp hb]
      exact id
    | cast k => exact wh _ (outside_root r reg k) (fun e h => mem_biUnion.mpr ⟨k,mem_univ _,h⟩)
  have right : Sᶜ.Nonempty := ⟨v,mem_compl.mpr nv⟩
  by_cases root : Fin.last 19∈S
  · have wc (j) : Cohesive (region r j) Sᶜ := by
      intro a ha b hb na
      exact mem_compl.mpr (fun bs => mem_compl.mp na (whole j b hb a ha bs))
    apply no_side r P reg orig share F fixed c Sᶜ right (by simpa using left) (by simpa using root) _ wc
    intro v hv
    exact mem_compl.mpr (fun h => mem_compl.mp hv (mate_involutive F c v ▸ cl _ h))
  · exact no_side r P reg orig share F fixed c S left right root cl whole

/-- Choosing the four colors already determines a single set of at most
thirteen wild edges that works simultaneously for every legal redraw. -/
theorem common_thirteen (P : Finset C) (four : P.card=4) :
    ∃ w : Lines 19,Legal w ∧ w.card≤13 ∧ ∀ g : Coloring 19 19, Fixed (augment (by decide) g) P → Works g w := by
  obtain ⟨reg,orig,share⟩ := four_checked P four
  obtain ⟨legal,sz⟩ := size_lines _ reg
  exact ⟨_,legal,sz,paths _ P reg orig share⟩

theorem exact_four (P : Finset C) (four : P.card=4) :
    (∀ g : Coloring 19 19,Fixed (augment (by decide) g) P → Exact g 13) ∧
    (∀ g : Coloring 20 19,Fixed g P → Exact g 13) := by
  obtain ⟨w,leg,sz,ok⟩ := common_thirteen P four
  constructor
  · intro g f
    have hw := ok g f
    exact ⟨⟨w,leg,Nat.le_antisymm sz (odd_lower (by decide) g leg hw),hw⟩,fun _ h p => odd_lower (by decide) g h p⟩
  · intro g f
    have ff : Fixed (augment (by decide) (restrict g)) P :=
      fun c nc v => (mate_augment_restrict (by decide) g c v).trans (f c nc v)
    obtain ⟨u,hu,nu,win⟩ := upper_from_deletion g (show Upper (restrict g) 13 from ⟨w,leg,sz,ok _ ff⟩)
    exact ⟨⟨u,hu,Nat.le_antisymm nu (even_lower (by decide) g hu win),win⟩,fun _ h p => even_lower (by decide) g h p⟩

#print axioms common_thirteen
#print axioms exact_four
end WildPalette
