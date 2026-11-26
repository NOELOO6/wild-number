import SixRows
import PlanSound
namespace SixColors
open EdgeWalk WildDeletion

theorem six_redrawn (p : Plan) (listed : p ∈ plans) (actual : List Item)
    (allowed : ∀ m ∈ actual, m ∈ pool p.root p.mask)
    (disjoint : ∀ a ∈ actual, ∀ m ∈ actual, compatible a m = true)
    (covers : ∀ i, (pool p.root p.mask).any (fun m => m.key.testBit i) = true →
      ∃ a ∈ actual, a.key.testBit i = true) :
    ∃ w : Edges, w.length = 10 ∧ (∀ m ∈ originals p.root, Connected (Adj (w++m))) ∧
      ∀ m ∈ actual, Connected (Adj (w++m.edges)) :=
  solve_plan p (List.all_eq_true.mp all_rows _ listed) actual allowed disjoint covers
def erasedBits (mask : Nat) := (List.range 15).foldl (fun u c =>
    if mask.testBit c then u ||| bits (original c) else u) 0

set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem possible_lines_are_erased : plans.all (fun p => (pool p.root p.mask).all fun m =>
    (m.key &&& erasedBits p.mask) == m.key) = true := by native_decide

/-- The inputs here are actual lists of pairs. Coverage requires that every
erased original line is colored again. -/
theorem six_from_edge_lists (p : Plan) (listed : p ∈ plans) (redrawn : List Raw)
    (matchings : ∀ m ∈ redrawn, Allowed p.mask (List.range 16) m ∧ m.length = 8)
    (proper : ∀ a ∈ redrawn, ∀ b ∈ redrawn, a = b ∨ bits a &&& bits b = 0)
    (covers : ∀ i, (erasedBits p.mask).testBit i = true →
      ∃ m ∈ redrawn, (bits m).testBit i = true) :
    ∃ w : Edges, w.length = 10 ∧
      ∀ m ∈ originals p.root ++ redrawn.map (erasePoint p.root), Connected (Adj (w++m)) := by
  let actual := redrawn.map (item p.root)
  have hsub (m : Item) (hm : m ∈ actual) : m ∈ pool p.root p.mask := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    obtain ⟨match',len⟩ := matchings a ha
    exact List.mem_map_of_mem (all_matchings match' 8 (Nat.le_of_eq len))
  have hdis (a : Item) (ha : a ∈ actual) (b : Item) (hb : b ∈ actual) : compatible a b = true := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    rcases proper x hx y hy with rfl | eq <;> simp_all [item,compatible]
  have hcov (i : Nat) (hi : (pool p.root p.mask).any (fun m => m.key.testBit i) = true) :
      ∃ a ∈ actual, a.key.testBit i = true := by
    obtain ⟨m,hm,has⟩ := List.any_eq_true.mp hi
    have sub := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp possible_lines_are_erased p listed) m hm)
    have hbit := congrArg (fun n : Nat => n.testBit i) sub
    simp only [Nat.testBit_and, has, Bool.true_and] at hbit
    obtain ⟨a,ha,good⟩ := covers i hbit
    exact ⟨item p.root a,List.mem_map_of_mem ha,good⟩
  obtain ⟨w,hw,old,new'⟩ := six_redrawn p listed actual hsub hdis hcov
  refine ⟨w,hw,fun m hm => ?_⟩
  rcases List.mem_append.mp hm with ho | hn
  · exact old m ho
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hn
    exact new' (item p.root a) (List.mem_map_of_mem ha)

theorem restored {w : Edges} {ms : List Edges} (paths : ∀ m ∈ ms, Connected (Adj (w++m)))
    (mate : Edges → Fin 15) :
    ∀ m ∈ ms, Connected (withLeaf (Adj (w++m)) (mate m)) :=
  fun m hm => (leaf_iff _ _).mpr (paths m hm)
#print axioms six_redrawn
#print axioms six_from_edge_lists
end SixColors
