import FourAnchor
import NineEncoding
import ThirteenData

namespace WildExact.K13
open WildExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem perRow (r : Row 13) (mem : r ∈ Rows 13) (good : repeatPair r=false) (k : Cap) (hk : k∈allCaps)
    (check : fastCheck=true) :
    ((blocked r).filter (fun i => (capList k).contains i)).length ≤
      base k + fee (coefficients k) r + factor k * penalty r := by
  obtain all := List.all_eq_true.mp check r mem
  simp only [good,Bool.false_or,Id.run] at all
  have yes := List.all_eq_true.mp all (budgetFor k) (List.mem_map.mpr ⟨k,hk,rfl⟩)
  dsimp only [budgetFor] at yes
  have valid : ∀ i, (((List.range 85).map (fun j => (capList k).contains j)).toArray[i]?.getD false) =
      (capList k).contains i := by
    intro i
    by_cases hi : i<85
    · simp [List.getElem?_eq_getElem,hi]
    · have no : i∉capList k := by
        intro h
        have := List.mem_range.mp (List.mem_filter.mp h).1
        omega
      have eq : (List.range 85)[i]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)
      simp [eq,no]
  have get {α : Type} {n} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f).get i = f i :=
    Vector.getElem_ofFn i.isLt
  simpa only [valid,get,fee,decide_eq_true_eq] using yes

def badFamily (rs : Fin 13 → Row 13) (i : Nat) :=
  (List.finRange 13).any (fun c => (blocked (rs c)).contains i)

private theorem below_sum {α} (xs : List α) (f : α → Int) (nn : ∀ a∈xs,0≤f a)
    (x : α) (mem : x∈xs) : f x ≤ totalI xs f := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    have tail := fun y hy => nn y (List.mem_cons_of_mem a hy)
    have nz : 0≤totalI xs f := by
      have := total_mono xs (f:=fun _ => 0) tail
      simpa [total_const] using this
    change f x ≤ f a+totalI xs f
    rcases List.mem_cons.mp mem with rfl|hm
    · omega
    · have := ih tail hm
      have := nn a (by simp)
      omega

private theorem countTotal {α} (xs : List α) (test : α → Bool) :
    ((xs.filter test).length : Int) = totalI xs (fun x => if test x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : test a <;> simp [List.filter_cons,h,totalI] at ih ⊢ <;> omega

private theorem mulTotal {α} (xs : List α) (f : α → Int) (v : Int) :
    totalI xs (fun x => v * f x) = v * totalI xs f := by
  induction xs with
  | nil => simp [totalI]
  | cons x xs ih => change v*f x + totalI xs (fun x => v*f x) = v*(f x + totalI xs f); rw [ih,Int.mul_add]

private theorem unionBound (rs : V → Row 13) (k : Cap) :
    ((capList k).filter (badFamily rs)).length ≤
      totalI (List.finRange 13) (fun c => (((blocked (rs c)).filter (fun i => (capList k).contains i)).length : Int)) := by
  classical
  let xs := capList k
  let cs := List.finRange 13
  let bit := fun (i : Nat) (c : V) => if (blocked (rs c)).contains i then (1:Int) else 0
  have nn (i c) : 0 ≤ bit i c := by simp [bit]; split <;> decide
  have single (i : Nat) : (if badFamily rs i then (1:Int) else 0) ≤ totalI cs (bit i) := by
    by_cases one : badFamily rs i=true
    · obtain ⟨c,hc,hit⟩ := List.any_eq_true.mp one
      have le := below_sum cs (bit i) (fun c _ => nn i c) c hc
      have val : bit i c=1 := if_pos hit
      simpa only [one,if_true,val] using le
    · have le := total_mono cs (f:=fun _ => 0) (fun c _ => nn i c)
      simpa [total_const,one] using le
  have nd : xs.Nodup := List.Nodup.filter _ List.nodup_range
  have localBound (c : V) : totalI xs (fun i => bit i c) ≤
      (((blocked (rs c)).filter (fun i => xs.contains i)).length : Int) := by
    let ys := blocked (rs c)
    have sub : (xs.filter (fun i => ys.contains i)).toFinset ⊆ (ys.filter (fun i => xs.contains i)).toFinset := by
      intro i
      simp [and_comm]
    have len := (List.toFinset_card_of_nodup (nd.filter (fun i => ys.contains i)))
    have l := le_trans (Finset.card_le_card sub) (List.toFinset_card_le _)
    rw [len] at l
    rw [← countTotal xs (fun i => ys.contains i)]
    exact_mod_cast l
  rw [countTotal]
  exact (total_mono xs (fun i _ => single i)).trans ((transpose xs cs bit) ▸ (total_mono cs (fun c _ => localBound c)))

theorem no_pair_of_weight (g : Coloring 13 13) (ok : Four.weight g 3<2) (rs : V → Row 13)
    (hr : ∀ c, rs c∈Rows 13 ∧ Respects (mate (augment (by decide) g) c) (rs c))
    (c : V) : repeatPair (rs c)=false := by
  let cs := List.finRange 13
  have read (c : V) : penalty (rs c) = Four.score (Four.graphEdge g c) (Four.graphStar g c) 0 1 2 3 := by
    obtain ⟨e,s⟩ := Four.row_reads g c _ (hr c).1 (hr c).2
    rw [penalty,e,s]
  have budget : totalI cs (fun c => penalty (rs c)) < 2 := by simpa only [read,Four.weight] using ok
  have nn (x : V) : 0 ≤ penalty (rs x) := by
    unfold penalty Four.score
    split <;> split <;> decide
  have le := below_sum cs _ (fun x _ => nn x) c (List.mem_finRange _)
  cases test : repeatPair (rs c) with
  | false => rfl
  | true =>
    simp only [repeatPair] at test
    have lo : 2 ≤ penalty (rs c) := by
      simp only [penalty,Four.score,test,if_true]; split <;> decide
    omega

theorem caps_of_graph (g : Coloring 13 13) (ok : Four.weight g 3<2) (rs : V → Row 13)
    (hr : ∀ c, rs c∈Rows 13 ∧ Respects (mate (augment (by decide) g) c) (rs c))
    (check : fastCheck=true) : Nine.Caps (badFamily rs) := by
  intro l mem
  have eq : Nine.limits = allCaps.map (fun k => (capList k,k.maximum)) := by native_decide
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (eq ▸ mem)
  let cs := List.finRange 13
  have read (c : V) : penalty (rs c) = Four.score (Four.graphEdge g c) (Four.graphStar g c) 0 1 2 3 := by
    obtain ⟨e,s⟩ := Four.row_reads g c _ (hr c).1 (hr c).2
    rw [penalty,e,s]
  have budget : totalI cs (fun c => penalty (rs c)) < 2 := by simpa only [read,Four.weight] using ok
  have no := no_pair_of_weight g ok rs hr
  have charges : ∀ k∈allCaps, ∀ e∈coefficients k,e.1.1≠e.1.2 := by native_decide
  have limit : ∀ k∈allCaps, 13*base k+totalI (coefficients k) Prod.snd+factor k ≤ k.maximum ∧ 0≤factor k := by native_decide
  have s := total_mono cs (fun c _ => perRow _ (hr c).1 (no c) k hk check)
  rw [total_add,total_add,total_const,fees_sum _ _ hr _ (charges _ hk),mulTotal] at s
  have cslen : cs.length=13 := List.length_finRange
  rw [cslen] at s
  obtain ⟨allow,pos⟩ := limit k hk
  have mul : factor k * totalI cs (fun c => penalty (rs c)) ≤ factor k :=
    by simpa using Int.mul_le_mul_of_nonneg_left (by omega : totalI cs (fun c => penalty (rs c)) ≤ 1) pos
  have bound := unionBound rs k
  change ((capList k).filter (badFamily rs)).length ≤ k.maximum
  dsimp only [cs] at s mul
  omega

end WildExact.K13
