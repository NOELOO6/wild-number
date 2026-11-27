import Periodic
namespace WildExact.Periodic
set_option autoImplicit false
variable {p k : Nat}

private def follow (p : Nat) (a : Pattern k) (s : Int) (u : State k) : List (State k) → Option (State k)
  | [] => some u
  | v::vs => if v ∈ advance p a s u then follow p a s v vs else none

private theorem follow_mem [NeZero k] (a : Pattern k) (s : Int) (u v : State k)
    (steps : List (State k)) (t : Nat) (hu : u∈reached p a s t)
    (h : follow p a s u steps=some v) : v∈reached p a s (t+steps.length) := by
  induction steps generalizing t u with
  | nil => simp [follow] at h; simpa [←h] using hu
  | cons x xs ih =>
    simp only [follow] at h
    split at h
    next hx =>
      have nx : x∈reached p a s (t+1) := List.mem_dedup.mpr (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨u,hu,hx⟩))
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih x (t+1) nx h
    next => contradiction

private theorem reach_le [NeZero k] (a : Pattern k) (s : Int) (v : State k)
    {t r : Nat} (found : v∈reached p a s t) (le : t≤r) : v∈reached p a s r := by
  induction le with
  | refl => exact found
  | step _ ih => exact List.mem_dedup.mpr (List.mem_append_left _ ih)

private def small : Pattern 1 := fun _ v => ([0,4,5] : List Int)[v.val]!
private def large : Pattern 3 := fun u v => (([[0,1,6],[3,5,11],[4,7,8]] : List (List Int))[u.val]!)[v.val]!

/-- At entry zero the route returns to a translated copy of the starting
triple. The other entries give a path to each other sort of triple. -/
private def smallRoutes (s : Fin 3) (i : Fin 1) : List (State 1) :=
  let rows : List (List (List (State 1))) := [
    [[(0,3),(0,6)]],
    [[(0,2),(0,4),(0,6)]],
    [[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]]]
  (rows[s.val]!)[i.val]!

private def largeRoutes (s : Fin 9) (i : Fin 3) : List (State 3) :=
  let rows : List (List (List (State 3))) := [
    [[(1,0),(1,1),(0,2)],[(1,-1)],[(2,-1)]],
    [[(1,0),(1,1),(0,2)],[(1,0)],[(2,-1)]],
    [[(2,0),(1,0),(0,1),(2,1),(1,1),(0,2)],[(1,-1)],[(2,0)]],
    [[(0,1),(0,2)],[(1,1)],[(2,-1)]],
    [[(0,1),(0,2)],[(1,-1)],[(2,-1)]],
    [[(0,1),(0,2)],[(1,-1)],[(2,-1)]],
    [[(1,0),(2,0),(1,1),(2,1),(0,2)],[(1,0)],[(2,-1)]],
    [[(1,0),(2,1),(0,2)],[(1,0)],[(2,-1)]],
    [[(1,1),(2,2),(0,2)],[(1,1)],[(2,0)]]]
  (rows[s.val]!)[i.val]!

private def good [NeZero k] (p : Nat) (a : Pattern k) (d : Nat)
    (w : Fin p → Fin k → List (State k)) (s : Fin p) (i : Fin k) : Bool :=
  (w s i).length≤6 && match follow p a s.val (0,0) (w s i) with
  | none => false
  | some v => v.1==i && (i != 0 || v.2==(d:Int))

private theorem read [NeZero k] (a : Pattern k) (d : Nat) (w : Fin p → Fin k → List (State k))
    (all : ∀ s i,good p a d w s i=true) (s : Fin p) :
    (0,(d:Int))∈reached p a s.val 6 ∧ ∀ i : Fin k, ∃ t : Int,(i,t)∈reached p a s.val 6 := by
  have get (i : Fin k) : ∃ t : Int,(i,t)∈reached p a s.val 6 ∧ (i=0 → t=d) := by
    have ok := all s i
    unfold good at ok
    obtain ⟨bound,h⟩ := Bool.and_eq_true_iff.mp ok
    split at h
    next => contradiction
    next v result =>
      obtain ⟨index,last⟩ := Bool.and_eq_true_iff.mp h
      have hv := follow_mem a _ (0,0) v (w s i) 0 (by simp [reached]) result
      have mem := reach_le a _ v hv (by simpa only [Nat.zero_add] using of_decide_eq_true bound)
      exact ⟨v.2,(eq_of_beq index) ▸ mem,fun hi => by simpa [hi] using last⟩
  obtain ⟨t,reaches,zero⟩ := get 0
  exact ⟨zero rfl ▸ reaches,fun i => (get i).imp fun _ h => h.1⟩

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

private theorem smallChecks : ∀ s i,good 3 small 6 smallRoutes s i=true := by decide
private theorem largeChecks : ∀ s i,good 9 large 2 largeRoutes s i=true := by decide

private theorem transport_upper {n n' b : Nat} [NeZero n] [NeZero n'] (eq : n=n')
    (upper : Upper (roundRobin n') b) : Upper (roundRobin n) b := by subst n'; exact upper

/-- The explicit round-robin coloring by the sum of the two endpoint labels
has wild number 2m on 3m points for every positive odd m. -/
theorem round_robin_triples (m : Nat) (hm : m%2=1) [NeZero (3*m)] :
    Exact (roundRobin (3*m)) (2*m) := by
  have pos : 0<m := by omega
  apply exact_of_upper
  · by_cases multiple : m%3=0
    · let t := m/3
      have mt : m=3*t := by dsimp [t]; omega
      have et : 3*m=9*t := by omega
      have odd : t%2=1 := by omega
      have positive : 0<t := by omega
      have unit : Nat.Coprime 2 t := by
        change Nat.gcd 2 t=1
        rw [Nat.gcd_rec,odd]; decide
      haveI : NeZero (9*t) := ⟨by omega⟩
      have bound := pattern_upper (p:=9) (m:=t) (by decide) positive large 2 6 unit
        (by decide) (read large 2 largeRoutes largeChecks)
      have b : 2*m=t*(3*2) := by omega
      rw [b]
      exact transport_upper et bound
    · have unit : Nat.Coprime 6 m := by
        change Nat.gcd 6 m=1
        rw [Nat.gcd_rec]
        have h : m%6=1 ∨ m%6=5 := by omega
        rcases h with h|h <;> rw [h] <;> decide
      have bound := pattern_upper (p:=3) (m:=m) (by decide) pos small 6 6 unit
        (by decide) (read small 6 smallRoutes smallChecks)
      simpa [Nat.mul_comm] using bound
  · intro w legal wins
    have bound := odd_lower (n:=3*m) (by omega) (roundRobin _) legal wins
    omega

#print axioms round_robin_triples
end WildExact.Periodic
