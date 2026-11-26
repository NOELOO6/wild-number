import Rows

namespace K17
set_option interpreter.prefer_native true
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Enumerate the possible even cycle lengths; the root cycle is distinguished. -/
def tails : Nat → Nat → Nat → List (List Nat)
  | 0, left, _ => if left == 0 then [[]] else []
  | fuel+1, left, least =>
    if left == 0 then [[]] else
      (List.range 10).flatMap fun k =>
        if least ≤ 2*k && 2*k ≤ left then
          (tails fuel (left-2*k) (2*k)).map (fun l => 2*k :: l)
        else []

def allTypes := (List.range 10).flatMap fun k =>
  if k < 2 then [] else (tails 3 (18-2*k) 4).map (fun l => 2*k :: l)

def gain (i : Nat) : Int := Id.run do
  let r := data[i]!
  let (a,b) := canonical r.cycles
  let mut total := 0
  for v in [:18] do
    for u in [:v] do
      if a[u]! != v && b[u]! != v then total := total+r.prices[edgeId u v]!
  return 10*(r.both : Int)-total

def transfer (i j k : Nat) := data[i]!.transfers[j]![k]!

theorem budgets :
    (chooseMasks 17 5).size * partitions.size = 95295200 ∧
    expectedThird.toList.sum = 173837682 ∧
    allTypes.length = 15 ∧ data.size = 15 ∧
    (allTypes.all fun t => (data.map Row.cycles).contains t) = true ∧
    (∀ i : Fin 15, typeTable[listKey data[i.val]!.cycles]! = i.val) ∧
    (∀ i : Fin 15, 3973540 ≤ gain i.val) ∧
    (∀ i j k : Fin 15, transfer i j k = transfer i k j ∧
       transfer i j k + transfer j i k + transfer k i j ≤ 1) := by native_decide

def two (k : Nat) : Nat := k*(k-1)/2
def three (k : Nat) : Nat := k*(k-1)*(k-2)/6
def survives (k : Nat) : Int := if k = 0 then 1 else 0

private theorem scalar (k : Fin 18) :
    12*(1-(k.val : Int)) + 10*(two k : Int) - 6*(three k : Int) ≤ 12*survives k := by
  exact (show ∀ j : Fin 18, 12*(1-(j.val : Int)) + 10*(two j : Int) -
    6*(three j : Int) ≤ 12*survives j from by decide) k

def total (xs : List (Fin 18)) (f : Fin 18 → Int) := (xs.map f).sum

/-- Apply the cubic bound to any distribution of bad-color counts. -/
theorem count_bound (xs : List (Fin 18)) :
    12*((xs.length : Int) - total xs (fun k => k.val)) +
      10*total xs (fun k => two k) - 6*total xs (fun k => three k) ≤
      12*total xs (fun k => survives k) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have h := scalar x
    simp only [total, List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one] at ih ⊢
    omega

/-- The triple budget and the first moment imply a strictly positive count. -/
theorem guaranteed_groupings (xs : List (Fin 18))
    (layouts : xs.length = 95295200)
    (singles : total xs (fun k => k.val) = 17*8230880)
    (tripleBudget : 6*total xs (fun k => three k) ≤
       10*total xs (fun k => two k) - 136*3973540 + 680) :
    403637 ≤ total xs (fun k => survives k) := by
  have h := count_bound xs
  rw [layouts, singles] at h
  omega

/-- Each triple appears in three different pair accounts. Its three transfer
    entries cancel to within one unit. -/
structure TripleAccount where
  i : Fin 15
  j : Fin 15
  k : Fin 15
  hit : Int
  feeA : Int
  feeB : Int
  feeC : Int

def fees (x : TripleAccount) := x.feeA+x.feeB+x.feeC
def paid (x : TripleAccount) :=
  2*x.hit ≤ x.feeA+transfer x.i x.j x.k ∧
  2*x.hit ≤ x.feeB+transfer x.j x.i x.k ∧
  2*x.hit ≤ x.feeC+transfer x.k x.i x.j

theorem cancel_transfers (ts : List TripleAccount) (ok : ∀ t ∈ ts, paid t) :
    6*(ts.map TripleAccount.hit).sum ≤ (ts.map fees).sum + (ts.length : Int) := by
  induction ts with
  | nil => decide
  | cons x xs ih =>
    have ⟨ha,hb,hc⟩ := ok x (by simp)
    have ht := (budgets.2.2.2.2.2.2.2 x.i x.j x.k).2
    have hs := ih (fun y hy => ok y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one, fees]
    omega

/-- Sum the 136 individual gains on any multiset of pair types. -/
def pairHits (t : Fin 15) : Int := data[t.val]!.both
def priceSum (t : Fin 15) := 10*pairHits t - gain t
theorem sum_prices (ps : List (Fin 15)) :
    (ps.map priceSum).sum ≤ 10*(ps.map pairHits).sum - (ps.length : Int)*3973540 := by
  induction ps with
  | nil => decide
  | cons x xs ih =>
    have h := budgets.2.2.2.2.2.2.1 x
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one, priceSum]
    omega

/-- The four double-counting identities are the bookkeeping bridge in the
    written proof. The conclusion follows for any matching factorization
    satisfying them and the three local price inequalities. -/
theorem combine (xs : List (Fin 18)) (ps : List (Fin 15)) (ts : List TripleAccount)
    (layoutCount : xs.length = 95295200) (pairCount : ps.length = 136)
    (tripleCount : ts.length = 680) (singles : total xs (fun k => k.val) = 17*8230880)
    (doubles : total xs (fun k => two k) = (ps.map pairHits).sum)
    (triples : total xs (fun k => three k) = (ts.map TripleAccount.hit).sum)
    (edgeCover : (ts.map fees).sum = (ps.map priceSum).sum)
    (localBounds : ∀ t ∈ ts, paid t) : 403637 ≤ total xs (fun k => survives k) := by
  apply guaranteed_groupings xs layoutCount singles
  rw [doubles, triples]
  have h := cancel_transfers ts localBounds
  have g := sum_prices ps
  rw [edgeCover,tripleCount] at h
  rw [pairCount] at g
  omega

#print axioms all_pair_types
#print axioms budgets
#print axioms combine
end K17
