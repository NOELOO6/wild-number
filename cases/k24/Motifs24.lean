import MotifRelabel30
import Mathlib.Data.Fintype.Card

namespace WildSieve.TwentyFour.Motifs
open Finset WildSieve.EdgeDeletion
open WildSieve.Thirty.Motifs (nodes center mapped map_bill nodes_mapped center_mapped sweep sweep_sound)

private abbrev Point := Fin 8
private abbrev Edge := Finset Point
def pairCost {α : Type} [DecidableEq α] (p : Finset (Finset α)) : Nat := if (nodes p).card=4 then 27 else 28

def tripleCredit {α : Type} [DecidableEq α] (p : Finset (Finset α)) : Nat :=
  match (nodes p).card with
  | 3 => 0
  | 4 => if center p then 13 else 14
  | 5 => 13
  | _ => 9

def wins {α : Type} [DecidableEq α] (S : Finset (Finset α)) : Bool :=
  decide (S.card=0 ∨ 42+bill pairCost 2 S≤42*S.card+bill tripleCredit 3 S)

private theorem wins_mapped {α β : Type} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (S : Finset (Finset α)) : wins (mapped f S)=wins S := by
  have hq := map_bill f S 2 pairCost pairCost (fun T => by simp only [pairCost,nodes_mapped,card_map])
  have hb := map_bill f S 3 tripleCredit tripleCredit (fun T => by
    simp only [tripleCredit,nodes_mapped,card_map,center_mapped])
  unfold wins
  rw [hq,hb]
  simp only [mapped,card_map]

private def deck : List Edge := do
  let a ← List.finRange 8
  let b ← List.finRange 8
  guard (a<b)
  pure {a,b}

private theorem mem_deck {e : Edge} (size : e.card=2) : e∈deck := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp size
  rcases lt_or_gt_of_ne ab with h|h
  · exact List.mem_flatMap.mpr ⟨a,List.mem_finRange _,List.mem_flatMap.mpr
      ⟨b,List.mem_finRange _,by simp [guard,h]⟩⟩
  · exact List.mem_flatMap.mpr ⟨b,List.mem_finRange _,List.mem_flatMap.mpr
      ⟨a,List.mem_finRange _,by simp [guard,h,pair_comm]⟩⟩

private def baseEdge : Edge := {0,1}
private def meeting : Edge := {0,2}
private def separate : Edge := {2,3}

/-- Number the shared endpoints first, then the other endpoints of each edge. -/
private def label (a b : Edge) (x : Point) : Point :=
  let v := List.finRange 8
  let ordered := v.filter (fun i => i∈a ∧ i∈b) ++ v.filter (fun i => i∈a ∧ i∉b) ++
    v.filter (fun i => i∉a ∧ i∈b) ++ v.filter (fun i => i∉a ∧ i∉b)
  Fin.ofNat' 8 (ordered.idxOf x)

private def normal (a b : Edge) : Bool :=
  decide (a=b ∨ ((∀ x y, label a b x=label a b y → x=y) ∧ a.image (label a b)=baseEdge ∧
    (b.image (label a b)=meeting ∨ b.image (label a b)=separate)))

private theorem checked :
    (deck.all fun a => deck.all (normal a))=true ∧
    sweep wins deck {baseEdge,meeting} 4=true ∧ sweep wins deck {baseEdge,separate} 4=true := by
  native_decide

private theorem with_roots (T : Finset Edge) (legal : T⊆deck.toFinset) (fit : T.card≤6)
    (a b : Edge) (ne : a≠b) (ab : {a,b}⊆T)
    (test : sweep wins deck {a,b} 4=true) : wins T=true := by
  let H : Finset Edge := {a,b}
  have hsize : H.card=2 := by simp [H,ne]
  have room : (T \ H).card≤4 := by rw [card_sdiff ab,hsize]; omega
  have result := sweep_sound wins deck H (T \ H) 4 (sdiff_subset.trans legal) room test
  simpa [union_eq_right.mpr (show H⊆T from ab)] using result

private theorem small_wins (T : Finset Edge) (proper : ∀ e∈T,e.card=2)
    (pos : 0<T.card) (fit : T.card≤6) : wins T=true := by
  by_cases single : T.card≤1
  · have none (k : Nat) (gt : 1<k) : T.powersetCard k=∅ := powersetCard_eq_empty.mpr (by omega)
    simp [wins,bill,none 2 (by decide),none 3 (by decide),show T.card=1 by omega]
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp (Nat.lt_of_not_ge single)
  have good := List.all_eq_true.mp (List.all_eq_true.mp checked.1 a (mem_deck (proper a ha))) b
    (mem_deck (proper b hb))
  obtain ⟨inject,first,second⟩ := (of_decide_eq_true good).resolve_left ne
  let f : Point ↪ Point := ⟨label a b,fun _ _ h => inject _ _ h⟩
  let U := mapped f T
  have sz : U.card≤6 := by simpa [U,mapped] using fit
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

/-- The weighted two- and three-edge comparison for any graph on eight vertices. -/
theorem finite_graph (S : Finset Edge) (edges : ∀ e∈S,e.card=2) (pos : 0<S.card) :
    42+bill pairCost 2 S≤42*S.card+bill tripleCredit 3 S := by
  apply lift_weighted _ _ 42 6 (by decide) _ _ _ pos
  · intro T _ many
    have cost (p) (_ : p∈T.powersetCard 2) : 27≤pairCost p := by unfold pairCost; split <;> decide
    have all := sum_le_sum cost
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_powersetCard] at all
    have choose : T.card.choose 2*2=T.card*(T.card-1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self T.card).two_dvd
    have bound := Nat.mul_le_mul_right (T.card-1) (show 7≤T.card by omega)
    unfold bill
    nlinarith only [all,choose,bound]
  intro T sub positive fit
  have yes := small_wins T (fun e he => edges e (sub he)) positive fit
  exact (of_decide_eq_true yes).resolve_left (Nat.ne_of_gt positive)

theorem graph_on_blocks {α : Type} [DecidableEq α] (L : Finset α) (order : L.card≤8)
    (S : Finset (Finset α)) (sizes : ∀ e∈S,e.card=2) (sub : ∀ e∈S,e⊆L) : wins S=true := by
  apply Thirty.Motifs.reduce_to_order L order S sizes sub (fun _ _ E => wins E)
    (fun _ _ _ _ f E => wins_mapped f E)
  intro H _ edges
  by_cases empty : H.card=0
  · exact decide_eq_true (Or.inl empty)
  · exact decide_eq_true (Or.inr (finite_graph H edges (Nat.pos_of_ne_zero empty)))

#print axioms finite_graph
end WildSieve.TwentyFour.Motifs
