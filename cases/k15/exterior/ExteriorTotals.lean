import ExteriorData
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Basic
namespace WildExterior
open Finset
abbrev Color := Fin 15
def rejected (P : Color → Pairs) (u : Color → Option Port) := univ.biUnion fun c => blocked (P c) (u c)

structure Accounts (P : Color → Pairs) (u : Color → Option Port) : Prop where
  prices : ∀ c,RowOK (P c) (u c)
  edges : (∑ c,(P c).card)=36
  roots : (∑ c,(star (u c)).card)=9
  atPort : ∀ x,(∑ c,if x∈used (P c) then 1 else 0)=8
  onSet : ∀ W : Finset Port,(∑ c,((star (u c))∩W).card)=W.card

private theorem union_degree (P : Color → Pairs) (u : Color → Option Port) (W : Finset Port) (t : Nat) :
    degree (rejected P u) W t ≤ ∑ c,degree (blocked (P c) (u c)) W t := by
  have sub : (rejected P u).filter (fun T => t≤(T∩W).card)⊆
      univ.biUnion (fun c => (blocked (P c) (u c)).filter (fun T => t≤(T∩W).card)) := by
    intro T h
    obtain ⟨c,_,tc⟩ := mem_biUnion.mp (mem_filter.mp h).1
    exact mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨tc,(mem_filter.mp h).2⟩⟩
  exact (card_le_card sub).trans card_biUnion_le

theorem common_caps {P : Color → Pairs} {u : Color → Option Port} (h : Accounts P u) :
    let B := rejected P u
    B.card≤31 ∧ (∀ x,degree B {x} 1≤18) ∧
      (∀ W : Finset Port,W.card=4 → degree B W 2≤24) ∧
      (∀ W : Finset Port,W.card=7 → degree B W 3≤22) := by
  have total := sum_le_sum (s:=univ) (fun c _ => (h.prices c).1)
  have c0 : (rejected P u).card≤∑ c,(blocked (P c) (u c)).card := card_biUnion_le
  simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,h.edges,h.roots] at total
  refine ⟨by omega,?_,?_,?_⟩
  · intro x
    have a := sum_le_sum (s:=univ) (fun c _ => (h.prices c).2.1 x)
    have b := union_degree P u {x} 1
    have cnt := h.onSet {x}
    have one (c) : ((star (u c))∩{x}).card=(if x∈star (u c) then 1 else 0) := by
      by_cases m : x∈star (u c) <;> simp [m,inter_comm]
    simp only [one,card_singleton] at cnt
    simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
      h.atPort,h.roots,cnt] at a
    omega
  · intro W sz
    have row := sum_le_sum (s:=univ) (fun c _ => (h.prices c).2.2.1 W (mem_powersetCard.mpr ⟨subset_univ _,sz⟩))
    have b := union_degree P u W 2
    simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,h.edges,h.roots] at row
    omega
  · intro W sz
    have row := sum_le_sum (s:=univ) (fun c _ => (h.prices c).2.2.2 W (mem_powersetCard.mpr ⟨subset_univ _,sz⟩))
    have b := union_degree P u W 3
    simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,h.edges,h.roots,h.onSet,sz] at row
    omega
end WildExterior
