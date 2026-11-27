import ClosedSides
import TypeTransport
namespace WildExact.Seventeen
open WildExact

def singleScore (a : V → V) := score (fun l => if lost a l then 1 else 0)
def pairScore (a b : V → V) := score (fun l => if shared a b l then 1 else 0)
def tripleScore (a b f : V → V) := score (fun l => if shared a b l && lost f l then 1 else 0)
def pay (i : Fin 15) (f : V → V) : Int := ∑ x,price i x (f x)

private theorem score_list {α} (xs : List α) (f : Layout → α → Nat) :
    score (fun l => natTotal xs (f l))=natTotal xs (fun s => score (fun l => f l s)) := by
  induction xs with
  | nil => simp [natTotal,score_univ]
  | cons s xs ih =>
    simp only [natTotal,List.map_cons,List.sum_cons,score_univ,Finset.sum_add_distrib] at ih ⊢
    rw [ih]

private theorem oneTerm {α} (xs : List α) (f : α → Nat) (s : α) (mem : s∈xs) :
    f s≤natTotal xs f := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    rcases List.mem_cons.mp mem with rfl|h
    · simp [natTotal]
    · exact (ih h).trans (Nat.le_add_left ..)

private theorem triple_cost (a b f : V → V) (r : Row 17) (owns : Respects f r)
    (all : (K17Connectivity.ends r).Perm (List.finRange 18)) :
    tripleScore a b f ≤ ((candidates r).map (valueAt (stats a b).frequency)).sum := by
  let term := fun l s => if shared a b l then (sides l).count s else 0
  have each (l : Layout) : (if shared a b l && lost f l then 1 else 0) ≤ natTotal (candidates r) (term l) := by
    split
    next yes =>
      obtain ⟨both,bad⟩ := Bool.and_eq_true_iff.mp yes
      obtain ⟨k,hk,closed⟩ := (loss_iff f l.1 l.2).mp ((lost_spec f l).mp bad)
      have mem : embed l.1 k∈sides l := List.mem_map.mpr ⟨k,hk,rfl⟩
      have cand := side_in_matching l f r owns all mem closed
      have pos : 1≤term l (embed l.1 k) := by simpa [term,both] using List.count_pos_iff.mpr mem
      exact pos.trans (oneTerm _ _ _ cand)
    next => exact Nat.zero_le _
  calc
    _ ≤ score (fun l => natTotal (candidates r) (term l)) := by
      simp only [tripleScore,score_univ]; exact Finset.sum_le_sum (fun l _ => each l)
    _ = _ := by
      rw [score_list]
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      exact (frequency_identity a b s (candidates_bounded r s hs)).symm

private theorem pay_eq (i : Fin 15) (f : V → V) (inv : Function.Involutive f)
    (r : Row 17) (owns : Respects f r) (all : (K17Connectivity.ends r).Perm (List.finRange 18)) :
    pay i f=2*edgeFee i r := by
  let cost := fun x => price i x (f x)
  have two (xs : Row 17) (h : Respects f xs) :
      ((K17Connectivity.ends xs).map cost).sum=2*edgeFee i xs := by
    induction xs with
    | nil => rfl
    | cons e xs ih =>
      obtain ⟨a,b⟩ := e
      have ab := h (a,b) (by simp)
      change f a=b at ab
      have ba : f b=a := ab ▸ inv a
      have sym : price i b a=price i a b := by unfold price edgeId; rw [max_comm b.val,min_comm b.val]
      have next := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      change cost a+(cost b+((K17Connectivity.ends xs).map cost).sum)=2*(price i a b+edgeFee i xs)
      rw [next]
      simp only [cost,ab,ba,sym]
      omega
  have equiv := (all.map cost).sum_eq
  rw [two r owns,←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange] at equiv
  exact equiv.symm

/-- Triples of failing colors satisfy the integer price inequality for each normalized pair and every possible third matching. -/
theorem canonical_triple (i : Fin 15) (f : V → V) (inv : Function.Involutive f) (free : ∀ x,x≠f x)
    (diffA : ∀ x,refA.get x≠f x) (diffB : ∀ x,(refB.get i).get x≠f x) (cert : certified i=true) :
    4*(tripleScore refA.get (refB.get i).get f : Int) ≤
      pay i f+2*transfer i (typeOf refA.get f) (typeOf (refB.get i).get f) := by
  obtain ⟨m,mem,owns⟩ := enumerate_complete f inv free 18 (List.finRange 18) (by decide) (List.nodup_finRange _) (by simp)
  have full := ends_cover 18 _ _ mem (List.nodup_finRange _)
  have rev : (K17Connectivity.ends m.reverse).Perm (List.finRange 18) :=
    (List.Perm.flatMap_right (fun e : V × V => [e.1,e.2]) (List.reverse_perm m)).trans full
  have rel : Respects f m.reverse := fun e h => owns e (List.mem_reverse.mp h)
  have cost := triple_cost refA.get (refB.get i).get f m.reverse rel rev
  have fee := closed_price i f inv diffA diffB m mem owns cert
  rw [pay_eq i f inv m.reverse rel rev]
  omega

end WildExact.Seventeen
