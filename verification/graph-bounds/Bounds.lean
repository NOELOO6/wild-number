import ColorCoordinates
import LegalEdges
import LowerBound
namespace WildCuts
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
open Finset EdgeWalk WildDeletion

def groups19 : Blocks (Fin 19) (Fin 6) where
  tag x := ⟨min (x.val/3) 5,by omega⟩
  rep i := ⟨3*i.val,by omega⟩
  section_ := by decide

def groups15 : Blocks (Fin 15) (Fin 5) where
  tag x := ⟨x.val/3,by omega⟩
  rep i := ⟨3*i.val,by omega⟩
  section_ := by decide

def groups16 : Blocks (Fin 16) (Fin 6) where
  tag x := ⟨(x.val+2)/3,by omega⟩
  rep i := ⟨3*i.val-2,by omega⟩
  section_ := by decide

def charge {n g : Nat} (b : Blocks (Fin n) (Fin g)) (r : Fin g) :=
  ∑ u : SideName (Fin g) r, ∑ j : Finset (Fin ((n+1)/2)),
    cost (side b u.1).card n (side (pairs n) j).card

def Solution {n : Nat} {C : Type} (m : C → List (Edge n)) (limit : Nat) :=
  ∃ w : List (Edge n), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length ≤ limit ∧
    ∀ c, Connected (Adj (w ++ m c))

theorem graph_bound {n k g cnum base : Nat} [Nontrivial (Fin n)]
    (b : Blocks (Fin n) (Fin g)) (r : Fin g) (m : Fin cnum → List (Edge n))
    (complete : ∀ x y : Fin n, x ≠ y → ∃ c, Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y = z)
    (size : n/2 = k) (total : Fintype.card (Line n) = cnum*k)
    (budget : cnum * charge b r < n.factorial * 3)
    (stars : (((List.finRange n).filter fun x => x != b.rep (b.tag x))).length = base) :
    Solution m (base+1) := by
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (coordinates size (by simpa using total) m complete proper)
  obtain ⟨p,a,z,az,paths⟩ := layout_and_repair b (pairs n) r m q hq (by simpa [charge] using budget)
  let es := (a,z)::wild b p
  have legal := tidy_properties es (by
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact az
    · exact wild_simple _ _ _ h)
  have len : es.length = base+1 := by simp [es,wild,stars]
  exact ⟨tidy es,legal.2.1,legal.2.2,legal.1.trans_eq len,fun c => tidy_connected es (m c) (paths c)⟩

theorem unrestricted_K19 (g : WildLower.Coloring (Fin 19)) : Solution g.edges 14 := by
  apply graph_bound (k := 9) (base := 13) groups19 0 _ g.complete g.proper (by decide)
  · decide +kernel
  · decide +kernel
  · decide

theorem unrestricted_K15 (m : Fin 15 → List (Edge 15))
    (complete : ∀ x y, x ≠ y → ∃ c, Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y = z) : Solution m 11 := by
  apply graph_bound (k := 7) (base := 10) groups15 0 _ complete proper (by decide)
  · decide +kernel
  · decide +kernel
  · decide

theorem unrestricted_K16 (m : Fin 15 → List (Edge 16))
    (complete : ∀ x y, x ≠ y → ∃ c, Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y = z) : Solution m 11 := by
  apply graph_bound (k := 8) (base := 10) groups16 0 _ complete proper (by decide)
  · decide +kernel
  · decide +kernel
  · decide

theorem thirteen_or_fourteen (g : WildLower.Coloring (Fin 19)) :
    ∃ w : List (Edge 19), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ (w.length = 13 ∨ w.length = 14) ∧
    (∀ c, Connected (Adj (w ++ g.edges c))) ∧
    ∀ u : List (Edge 19), (∀ e ∈ u, e.1 ≠ e.2) → (∀ c, Connected (Adj (u ++ g.edges c))) → 13 ≤ u.length := by
  obtain ⟨w,unique,lines,upper,paths⟩ := unrestricted_K19 g
  have lower := WildLower.thirteen_necessary g w (fun e he => (lines e he).ne) paths
  exact ⟨w,unique,lines,by omega,paths,WildLower.thirteen_necessary g⟩

#print axioms thirteen_or_fourteen
#print axioms unrestricted_K15
#print axioms unrestricted_K16
end WildCuts
