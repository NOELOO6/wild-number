import SparseEight
namespace EightPoints
def readExample (s : String) := ((s.splitOn "\n").filter (· != "")).map fun l =>
  parseEdges ((l.splitOn " ").map String.toNat!)
def firstExample := readExample (include_str "local-completion.txt")
def secondExample := readExample (include_str "asymmetric-completion.txt")
def properExample (ms : List Raw) := ms.length == 15 && ms.all (fun m =>
    m.length == 8 && (List.range 16).all fun x => m.any (fun (a,b) => a == x || b == x)) &&
  (List.range 16).all fun b => (List.range b).all fun a => ms.any (fun m => m.contains (a,b))
def extendsTable (ps ms : List Raw) := ps.length == ms.length &&
  (ps.zip ms).all (fun (p,m) => (completions p).contains m)
def edgeSet (w : Edges) := w.foldl (fun n (a,b) =>
  let hi := max a.val b.val
  let lo := min a.val b.val
  n ||| 2^(hi*(hi-1)/2+lo)) 0
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option interpreter.prefer_native true
theorem actual_examples : properExample firstExample = true ∧ properExample secondExample = true ∧
    extendsTable patterns firstExample = true ∧ extendsTable asymTable secondExample = true := by native_decide
theorem different_edge_sets : (layouts.map edgeSet).Nodup := by native_decide
theorem twenty_two_survive (cs : List (Raw × Raw)) (chart : cs.map Prod.fst = asymTable)
    (allowed : ∀ c ∈ cs, c.2 ∈ completions c.1) : 22 ≤ (surviving cs).length := by
  have b := completion_bound cs allowed
  have paid : spent cs = 48 := by
    change (cs.map (fun c => cost c.1)).sum = 48
    rw [show cs.map (fun c => cost c.1) = (cs.map Prod.fst).map cost by simp only [List.map_map, Function.comp_def],
      chart,full_costs]
    decide
  rw [seventy.1,paid] at b
  omega
#print axioms actual_examples
#print axioms twenty_two_survive
end EightPoints
