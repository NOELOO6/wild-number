import EightCertificate
namespace EightPoints
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def asymTable := (((include_str "asymmetric-table.txt").splitOn "\n").filter (· != "")).map fun l =>
  parseEdges ((l.splitOn " ").map String.toNat!)
def gaps : Raw := [(0,3),(2,3),(0,4),(2,4)]
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | x::xs => let tail := subsets xs; tail ++ tail.map (x :: ·)
def candidatePatterns (p : Raw) :=
  let fixed := p.filter (fun e => !gaps.contains e)
  ((subsets gaps).map (fixed ++ ·)).filter fun q =>
    (q.flatMap fun (a,b) => [a,b]).Nodup
def families := asymTable.map candidatePatterns
def allowance (f : List Raw) := ceiling (f.map cost)
theorem sparse_costs : families.map allowance = [0,0,10,8,8,4,8,0,4,8,8,0,0,8,0] := by native_decide
theorem pinned_count : (asymTable.flatten.filter (fun e => !gaps.contains e)).length = 32 ∧
    asymTable.flatten.Nodup := by native_decide
theorem full_costs : asymTable.map cost = [0,0,8,8,8,4,4,0,4,0,8,0,0,4,0] := by native_decide

private theorem affordable {f : List Raw} {p} (h : p ∈ f) : cost p ≤ allowance f := by
  induction f with
  | nil => contradiction
  | cons a f ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

abbrev Pick := List Raw × (Raw × Raw)
private theorem charge_choices (xs : List Pick) (h : ∀ x ∈ xs, x.2.1 ∈ x.1) :
    spent (xs.map Prod.snd) ≤ ((xs.map Prod.fst).map allowance).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    exact Nat.add_le_add (affordable (h x (by simp))) (ih (fun t ht => h t (by simp [ht])))

/-- The four listed local edges and every edge meeting the seven still-free
vertices may be recolored. Each chosen profile and full color may vary. -/
theorem four_survive_32_fixed (xs : List Pick) (chart : xs.map Prod.fst = families)
    (options : ∀ x ∈ xs, x.2.1 ∈ x.1) (allowed : ∀ x ∈ xs, x.2.2 ∈ completions x.2.1) :
    4 ≤ (surviving (xs.map Prod.snd)).length ∧ (surviving (xs.map Prod.snd)).Nodup ∧
      ∀ w ∈ surviving (xs.map Prod.snd), w.length = 10 ∧
        ∀ c ∈ xs.map Prod.snd, Connected (Adj (w ++ withoutRoot c.2)) := by
  have good : ∀ c ∈ xs.map Prod.snd, c.2 ∈ completions c.1 := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    exact allowed x hx
  have b := completion_bound (xs.map Prod.snd) good
  have paid := charge_choices xs options
  rw [chart,sparse_costs] at paid
  change spent (xs.map Prod.snd) ≤ 66 at paid
  rw [seventy.1] at b
  exact ⟨by omega,seventy.2.1.filter _,fun _ hw => genuine_paths _ hw⟩
#print axioms four_survive_32_fixed
end EightPoints
