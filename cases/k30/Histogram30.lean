import FrameIncidence30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) histEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

private theorem block_restriction (D : Deck) (L : Finset V) (seen : D∈localSeal univ L) (P : Pattern)
    (sub : P⊆D.val) : vertices (P.filter (·⊆L))=vertices P∩L := by
  ext v
  constructor
  · intro h
    obtain ⟨b,hb,vb⟩ := mem_biUnion.mp h
    exact mem_inter.mpr ⟨block_sub (mem_filter.mp hb).1 vb,(mem_filter.mp hb).2 vb⟩
  · intro h
    obtain ⟨vP,vL⟩ := mem_inter.mp h
    obtain ⟨b,bP,vb⟩ := mem_biUnion.mp vP
    exact mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨bP,(seal_whole (subset_univ _) D).mp seen b (sub bP) v vb vL⟩,vb⟩

theorem histogram_bound (F : Factor V C) (L : Finset V) (l : L.card=12) (D : Deck)
    (seen : D∈localSeal univ L) (t : Fin 3) : (sideHits F L D t).card≤(Nat.choose 4 (2-t.val))*(Nat.choose 6 t.val) := by
  classical
  let B := D.val.filter (·⊆L)
  let R := D.val \ B
  have sizeD := D.property.1.card_vertices
  rw [D.property.2,card_univ,Fintype.card_fin] at sizeD
  have sizeB := (D.property.1.sub (filter_subset (fun b => b⊆L) D.val)).card_vertices
  rw [block_restriction D L seen D.val Subset.rfl,D.property.2,univ_inter,l] at sizeB
  have b4 : B.card=4 := by change (D.val.filter (·⊆L)).card=4; omega
  have r6 : R.card=6 := by change (D.val \ B).card=6; rw [card_sdiff (show B⊆D.val from filter_subset _ _),b4]; omega
  let pair (P : Pattern) := (P∩B,P \ B)
  have valid (P : Pattern) (hp : P∈present F L D t) :
      pair P∈(B.powersetCard (2-t.val))×ˢ(R.powersetCard t.val) := by
    obtain ⟨m,kind,sub⟩ := (present_mem seen).mp hp
    have ok := (SixCounts.pattern_mem.mp m).1
    have num := SixCounts.pattern_size m
    have eq : P∩B=P.filter (·⊆L) := by ext b; simp only [B,mem_inter,mem_filter]; exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,sub h.1,h.2⟩⟩
    have cut := (ok.sub (filter_subset (fun b => b⊆L) P)).card_vertices
    rw [block_restriction D L seen P sub,kind,←eq] at cut
    have rem := card_sdiff_add_card_inter P B
    have limit := t.isLt
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right,by change (P∩B).card=2-t.val; omega⟩,
      mem_powersetCard.mpr ⟨(fun _ h => mem_sdiff.mpr ⟨sub (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩),by change (P \ B).card=t.val; omega⟩⟩
  have inj : Function.Injective pair := by
    intro P Q eq
    have a := congrArg Prod.fst eq
    have b := congrArg Prod.snd eq
    change P∩B=Q∩B at a
    change P \ B=Q \ B at b
    ext v
    by_cases h : v∈B
    · simpa [h] using Finset.ext_iff.mp a v
    · simpa [h] using Finset.ext_iff.mp b v
  have tally := sum_present F L D t seen (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at tally
  have equal : (sideHits F L D t).card=(present F L D t).card := by exact_mod_cast tally
  rw [equal,←card_image_of_injective _ inj]
  have cap := card_le_card (image_subset_iff.mpr valid)
  simpa [card_product,card_powersetCard,b4,r6] using cap

theorem histogram_column (F : Factor V C) (L : Finset V) (l : L.card=12) (D : Deck) (seen : D∈localSeal univ L) :
    Column.hist (sideHits F L D 0).card (sideHits F L D 1).card (sideHits F L D 2).card ∈columns := by
  have a := histogram_bound F L l D seen 0
  have b := histogram_bound F L l D seen 1
  have c := histogram_bound F L l D seen 2
  change _≤6 at a
  change _≤24 at b
  change _≤15 at c
  unfold columns
  simp only [List.mem_append]
  left; left; left; left; left
  simp only [List.bind_eq_flatMap,List.mem_flatMap,List.mem_range,List.mem_singleton]
  exact ⟨(sideHits F L D 0).card,by omega,(sideHits F L D 1).card,by omega,
    (sideHits F L D 2).card,by omega,by simp⟩

end WildSieve.Thirty.Graph
