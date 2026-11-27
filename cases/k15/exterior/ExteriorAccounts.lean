import ExteriorPorts
import ExteriorPrices
namespace WildExterior
open Finset WildSieve
private theorem gap_of_sizes {A C : Type} [LinearOrder A] [Fintype A] (F : Factor A C)
    (Y Z : Finset A) (partition : ∀ x,x∈Z ↔ x∉Y) (y9 : Y.card=9) (z7 : Z.card=7)
    (c : C) (rule : Inside F c Z≤2) : Inside F c Y=Inside F c Z+1 := by
  have eq : Z=Yᶜ := by ext x; exact (partition x).trans mem_compl.symm
  subst Z
  have a := free_pair_size (F.invol c) (F.moving c) Yᶜ
  rw [compl_compl] at a
  change 2*Inside F c Y=Y.card-(Yᶜ.card-2*Inside F c Yᶜ) at a
  rw [y9,z7] at a
  omega

private theorem edge_inside {A C : Type} [LinearOrder A] (F : Factor A C) (Z : Finset A) (c : C)
    (r : A) (hr : r∈Z) (hs : F.f c r∈Z) : 0<Inside F c Z := by
  apply card_pos.mpr
  rcases lt_or_gt_of_ne (F.moving c r) with lt|gt
  · exact ⟨r,mem_filter.mpr ⟨hr,lt,hs⟩⟩
  · refine ⟨F.f c r,mem_filter.mpr ⟨hs,?_,?_⟩⟩
    · rwa [F.invol c r]
    · rwa [F.invol c r]

theorem ordinary_gap (F : Factor V Color) (i : Port ↪ V) (rule : ∀ c,Inside F c (outside i)ᶜ≤2)
    (c : Color) : (ordinary F i c).card=Inside F c (outside i)ᶜ+1 :=
  (ordinary_counts F i c).2.trans (gap_of_sizes F _ _ (fun _ => mem_compl) (nine i) (seven i) c (rule c))

theorem account_graph (F : Factor V Color) (i : Port ↪ V) (r : V) (out : r∉outside i)
    (rule : ∀ c,Inside F c (outside i)ᶜ≤2) : Accounts (ordinary F i) (tap F i r) := by
  classical
  let Y := outside i
  have count (c) : (ordinary F i c).card=Inside F c Y := (ordinary_counts F i c).2
  have gap := ordinary_gap F i rule
  refine ⟨fun c => ?_,?_,?_,?_,tap_set F i r out⟩
  · have k := gap c
    change (ordinary F i c).card=Inside F c Yᶜ+1 at k
    have hi := rule c
    change Inside F c Yᶜ≤2 at hi
    apply row_prices (row_mem _ (fun _ he => (ordinary_mem.mp he).1) (by omega) (by omega) (ordinary_counts F i c).1)
    refine ⟨disjoint_left.mpr (fun x hx hu => ?_),fun n => ?_⟩
    · have eq := (tap_spec F i r c x).mp hx
      have m := (inside_partners F i c x).mp hu
      rw [eq,F.invol c r] at m
      exact out m
    · have away : F.f c r∉Y := by
        intro h
        obtain ⟨x,e⟩ := outside_mem.mp h
        have hit := (tap_spec F i r c x).mpr e
        simp [n,star] at hit
      have inside := edge_inside F Yᶜ c r (mem_compl.mpr out) (mem_compl.mpr away)
      omega
  · rw [sum_congr rfl (fun c _ => count c),sum_inside,nine]
    decide
  · simpa using tap_set F i r out univ
  · intro x
    have eq : (univ.filter (fun c => x∈used (ordinary F i c)))=univ.filter (fun c => F.f c (i x)∈Y) := by
      ext c;simp [inside_partners,Y]
    rw [sum_boole,eq,partners_in,card_erase_of_mem (port_inside i x),nine]
    rfl
end WildExterior
