import MotifRelabel30
import Mathlib.Data.Fintype.Card

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion

private abbrev Point := Fin 10
private abbrev Edge := Finset Point
private def baseEdge : Edge := {0,1}
private def meeting : Edge := {0,2}
private def separate : Edge := {2,3}

/-- Number the shared endpoints first, then the other endpoints of each edge. -/
private def label (a b : Edge) (x : Point) : Point :=
  let v := List.finRange 10
  let ordered := v.filter (fun i => i∈a ∧ i∈b) ++ v.filter (fun i => i∈a ∧ i∉b) ++
    v.filter (fun i => i∉a ∧ i∈b) ++ v.filter (fun i => i∉a ∧ i∉b)
  Fin.ofNat' 10 (ordered.idxOf x)

private def normal (a b : Edge) : Bool :=
  decide (a=b ∨ ((∀ x y, label a b x=label a b y → x=y) ∧ a.image (label a b)=baseEdge ∧
    (b.image (label a b)=meeting ∨ b.image (label a b)=separate)))

private theorem checked :
    (deck.all fun a => deck.all (normal a))=true ∧
    sweep wins deck {baseEdge,meeting} 3=true ∧ sweep wins deck {baseEdge,separate} 3=true := by
  native_decide

private theorem with_roots (T : Finset Edge) (legal : T⊆deck.toFinset) (fit : T.card≤5)
    (a b : Edge) (ne : a≠b) (ab : {a,b}⊆T)
    (test : sweep wins deck {a,b} 3=true) : wins T=true := by
  let H : Finset Edge := {a,b}
  have hsize : H.card=2 := by simp [H,ne]
  have room : (T \ H).card≤3 := by rw [card_sdiff ab,hsize]; omega
  have result := sweep_sound wins deck H (T \ H) 3 (sdiff_subset.trans legal) room test
  simpa [union_eq_right.mpr (show H⊆T from ab)] using result

private theorem small_wins (T : Finset Edge) (proper : ∀ e∈T,e.card=2)
    (pos : 0<T.card) (fit : T.card≤5) : wins T=true := by
  by_cases single : T.card≤1
  · have none (k : Nat) (gt : 1<k) : T.powersetCard k=∅ := powersetCard_eq_empty.mpr (by omega)
    simp [wins,bill,none 2 (by decide),none 3 (by decide),show T.card=1 by omega]
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge single)
  have good := List.all_eq_true.mp (List.all_eq_true.mp checked.1 a (mem_deck (proper a ha))) b
    (mem_deck (proper b hb))
  obtain ⟨inject,first,second⟩ := (of_decide_eq_true good).resolve_left ne
  let f : Point ↪ Point := ⟨label a b,fun _ _ h => inject _ _ h⟩
  let U := mapped f T
  have sz : U.card≤5 := by simpa [U,mapped] using fit
  have legal : U⊆deck.toFinset := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := mem_map.mp he
    apply List.mem_toFinset.mpr
    apply mem_deck
    exact card_map _ |>.trans (proper q hq)
  have inc (q : Edge) (hq : q∈T) : q.image (label a b)∈U := by
    have h : q.map f∈U := mem_map.mpr ⟨q,hq,rfl⟩
    simpa only [Finset.map_eq_image] using h
  have inside := first ▸ inc a ha
  rw [←wins_mapped f T]
  rcases second with same|apart
  · exact with_roots U legal sz baseEdge meeting (by decide)
      (insert_subset inside (singleton_subset_iff.mpr (same ▸ inc b hb))) checked.2.1
  · exact with_roots U legal sz baseEdge separate (by decide)
      (insert_subset inside (singleton_subset_iff.mpr (apart ▸ inc b hb))) checked.2.2

/-- The weighted two- and three-edge comparison for any graph on ten vertices. -/
theorem finite_graph (S : Finset Edge) (edges : ∀ e∈S,e.card=2) (pos : 0<S.card) :
    6+bill pairCost 2 S≤6*S.card+bill tripleCredit 3 S := by
  apply lift_five _ _ _ (fun p _ => by unfold pairCost; split <;> decide) _ pos
  intro T sub positive fit
  have yes := small_wins T (fun e he => edges e (sub he)) positive fit
  exact (of_decide_eq_true yes).resolve_left (Nat.ne_of_gt positive)

#print axioms finite_graph
end WildSieve.Thirty.Motifs
