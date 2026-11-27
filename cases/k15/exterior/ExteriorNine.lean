import ExteriorTotals
import NineTrace
import TripleCounts
namespace WildExterior
open Finset WildExact WildSieve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bits9 (s : Nat) : Finset Port := univ.filter (fun x => s.testBit x.val)
def triple (i : Nat) := bits9 (Nine.mask i)
private structure Test where
  ids : List Nat
  zone : Finset Port
  depth : Nat
  limit : Nat
private def tests : List Test := ⟨Nine.ids,∅,0,35⟩ :: (List.range 512).flatMap fun s =>
  ([(1,1,23),(4,2,30),(7,3,33)] : List (Nat × Nat × Nat)).filterMap fun (k,t,b) =>
    if Nine.bits s=k then some ⟨Nine.ids.filter (fun i => Nine.bits (Nine.mask i &&& s)≥t),bits9 s,t,b⟩ else none
private def correct (k : Test) : Prop :=
    (k.ids.map triple).Nodup ∧ (∀ i∈k.ids,k.depth≤(triple i∩k.zone).card) ∧
    ((k.depth=0 ∧ k.limit=35) ∨ (k.depth=1 ∧ k.zone.card=1 ∧ k.limit=23) ∨
     (k.depth=2 ∧ k.zone.card=4 ∧ k.limit=30) ∨ (k.depth=3 ∧ k.zone.card=7 ∧ k.limit=33))
private instance (k : Test) : Decidable (correct k) := by unfold correct;infer_instance
private theorem test_ids : Nine.limits=tests.map (fun k => (k.ids,k.limit)) := by native_decide
private theorem test_pass : tests.all (fun k => decide (correct k))=true := by native_decide

private def threeBlocks (i j k : Nat) := ({triple i,triple j,triple k}:Blocks Port)
private def real (i j k : Nat) : Bool :=
  let A := triple i
  let B := triple j
  let C := triple k
  decide (A.card=3 ∧ B.card=3 ∧ C.card=3 ∧ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A∪B∪C=univ)
private theorem real_checks : Nine.ids.all (fun i => Nine.ids.all (fun j => Nine.ids.all (fun k =>
    !Nine.hit i j k || real i j k)))=true := by native_decide

private theorem to_layout {i j k : Nat} (h : Nine.hit i j k=true) :
    Triples (threeBlocks i j k) ∧ vertices (threeBlocks i j k)=univ := by
  have shape := h
  simp only [Nine.hit,Bool.and_eq_true,decide_eq_true_eq] at shape
  have good := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp real_checks i
    (List.mem_range.mpr (by omega))) j (List.mem_range.mpr (by omega))) k (List.mem_range.mpr (by omega))
  simp only [h,Bool.not_true,Bool.false_or,real,decide_eq_true_eq] at good
  obtain ⟨a,b,c,ab,ac,bc,tot⟩ := good
  let A := triple i
  let B := triple j
  let C := triple k
  have eq : threeBlocks i j k=({A}:Blocks Port)∪{B}∪{C} := by ext;simp [threeBlocks,A,B,C,or_assoc]
  rw [eq]
  have t := (singleton_triple a).combine (singleton_triple b) (by simpa using ab)
  have d : Disjoint (vertices (({A}:Blocks Port)∪{B})) (vertices ({C}:Blocks Port)) := by
    simpa using disjoint_union_left.mpr ⟨ac,bc⟩
  exact ⟨t.combine (singleton_triple c) d,by simpa [A,B,C] using tot⟩

private theorem add_cost (B E : Finset (Finset Port)) (Z : Finset Port) (t : Nat) :
    degree (B∪E) Z t≤degree B Z t+E.card := by
  unfold degree
  rw [filter_union]
  exact (card_union_le _ _).trans (Nat.add_le_add_left (card_le_card (filter_subset _ E)) _)

private theorem ids_count (k : Test) (hk : correct k) (H : Finset (Finset Port)) :
    (k.ids.filter (fun i => decide (triple i∈H))).length≤degree H k.zone k.depth := by
  classical
  let l := k.ids.filter (fun i => decide (triple i∈H))
  have sub : (l.map triple).Sublist (k.ids.map triple) := (List.filter_sublist ..).map triple
  have nd := hk.1.sublist sub
  rw [show (k.ids.filter (fun i => decide (triple i∈H))).length=(l.map triple).length by simp [l],
    ←List.toFinset_card_of_nodup nd]
  apply card_le_card
  intro T ht
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
  obtain ⟨mem,flag⟩ := List.mem_filter.mp hi
  exact mem_filter.mpr ⟨of_decide_eq_true flag,hk.2.1 i mem⟩

/-- Up to four prescribed triples may be discarded in addition to all
common obstructions. The remaining nine vertices can still be partitioned. -/
theorem exterior_layout {P : Color → Pairs} {u : Color → Option Port} (h : Accounts P u)
    (E : Finset (Finset Port)) (four : E.card≤4) :
    ∃ L : Layout (univ : Finset Port),∀ T∈L.val,T∉rejected P u ∧ T∉E := by
  classical
  let B := rejected P u
  let H := B∪E
  let b (i : Nat) := decide (triple i∈H)
  have ⟨c0,c1,c4,c7⟩ := common_caps h
  have caps : Nine.Caps b := by
    intro l mem
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (test_ids ▸ mem)
    have ok := of_decide_eq_true (List.all_eq_true.mp test_pass k hk)
    have a := (ids_count k ok H).trans (add_cost B E k.zone k.depth)
    change (k.ids.filter b).length≤degree B k.zone k.depth+E.card at a
    change (k.ids.filter b).length≤k.limit
    rcases ok.2.2 with ⟨z,v⟩|⟨z,w,v⟩|⟨z,w,v⟩|⟨z,w,v⟩
    · have d : degree B k.zone k.depth=B.card := by simp [degree,z]
      change B.card≤31 at c0
      rw [d] at a
      omega
    · obtain ⟨x,xe⟩ := card_eq_one.mp w
      have d : degree B k.zone k.depth≤18 := by rw [xe,z];exact c1 x
      omega
    · have d : degree B k.zone k.depth≤24 := z.symm ▸ c4 k.zone w
      omega
    · have d : degree B k.zone k.depth≤22 := z.symm ▸ c7 k.zone w
      omega
  have ok := Nine.nine_points b caps
  unfold Nine.Hits at ok
  push_neg at ok
  obtain ⟨i,j,k,hit,ai,aj,ak⟩ := ok
  refine ⟨⟨_,to_layout hit⟩,?_⟩
  intro T ht
  have inv (q) (a : b q≠true) : triple q∉B ∧ triple q∉E := by simpa [b,H] using a
  simp only [threeBlocks,mem_insert,mem_singleton] at ht
  rcases ht with rfl|rfl|rfl
  · exact inv i ai
  · exact inv j aj
  · exact inv k ak
end WildExterior
