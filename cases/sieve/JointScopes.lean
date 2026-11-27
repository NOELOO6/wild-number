import JointDegrees
import FrozenLayout
namespace WildSieve
open Finset
local instance (priority := 2000) jointScopeFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

def jointDegree (n t u b j : Nat) :=
  let g := n+1-u
  let old := degBound n 0 t u j
  if g<u ∧ 0<g/2 then
    min old (if j=1 then (u-g)+(u-g)/2+b else chordPrice g u b)
  else old

def jointLimit (n u : Nat) :=
  let g := n+1-u
  if g<u ∧ 0<g/2 then g+g/2 else 0

private theorem ambient_degree {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]
    (F : Factor A C) (B : Finset A) (r : A) (hr : r∈B) (t j : Nat)
    (U : Finset (Free B)) (z : Free B) :
    (active (badScopes F B r 0 t j) U z).card ≤
      ((sides F (if Odd j then {r} else ∅) (U.map (emb B)) (3*j)).filter (fun X => z.val∈X)).card := by
  classical
  apply card_le_card_of_injOn (Finset.map (emb B)) _ (Finset.map_injective _).injOn
  intro X hx
  obtain ⟨bad,xu,zx⟩ := mem_filter.mp hx
  obtain ⟨D,hd,xd⟩ := (mem_gather _ _ _).mp bad
  obtain ⟨sz,c,cl⟩ := pull_mem.mp xd
  have root_out : r∉X.map (emb B) := fun h => mem_compl.mp (map_free B X h) hr
  have pc := closed_size (F.invol c) (F.moving c) cl
  have eq : D=(if Odd j then {r} else ∅) := by
    simp [choices] at hd
    rcases hd with rfl|rfl
    · rw [empty_union,card_map,sz] at pc
      have even : ¬Odd j := by rintro ⟨a,ha⟩; omega
      simp [even]
    · rw [show {r}∪X.map (emb B)=insert r (X.map (emb B)) by ext v; simp,card_insert_of_not_mem root_out,card_map,sz] at pc
      have odd : Odd j := ⟨j/2,by omega⟩
      simp [odd]
  exact mem_filter.mpr ⟨side_mem.mpr ⟨c,candidate_mem.mpr
    ⟨map_subset_map.mpr xu,by simpa using sz,eq ▸ cl⟩⟩,mem_map.mpr ⟨z,zx,rfl⟩⟩

theorem joint_scope_bounds {n : Nat} (F : Factor (Fin (n+1)) (Fin n)) (B : Finset (Fin (n+1)))
    (r : Fin (n+1)) (hr : r∈B) (t : Nat) (bs : B.card=1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (U : Finset (Free B)) (z : Free B) (hz : z∈U) :
    ∃ b≤jointLimit n U.card,∀ j∈shortLevels,
      (active (badScopes F B r 0 t j) U z).card≤jointDegree n t U.card b j := by
  classical
  let W := U.map (emb B)
  let g := n+1-U.card
  have wu : W.card=U.card := card_map _
  have wg : Wᶜ.card=g := by rw [card_compl,Fintype.card_fin,wu]
  have old (j) := bad_scope_degree F B r 0 t hr bs ws rain U z hz j
  simp only [Fintype.card_fin] at old
  by_cases ok : g<U.card ∧ 0<g/2
  · have zr : z.val∈W := mem_map.mpr ⟨z,hz,rfl⟩
    have rr : r∉W := fun h => mem_compl.mp (map_free B U h) hr
    obtain ⟨b,limit,one,two⟩ := joint_degrees F W r z.val rr zr (by rw [wg,wu]; exact ok.1) (by rw [wg]; exact ok.2)
    rw [wg,wu] at one two
    rw [wg] at limit
    refine ⟨b,by change b≤if g<U.card ∧ 0<g/2 then _ else _; rwa [if_pos ok],fun j hj => ?_⟩
    change _≤if g<U.card ∧ 0<g/2 then min _ _ else _
    rw [if_pos ok]
    refine Nat.le_min.mpr ⟨old j,?_⟩
    have c := ambient_degree F B r hr t j U z
    rcases (show j=1 ∨ j=2 by simpa only [shortLevels,mem_insert,mem_singleton] using hj) with rfl|rfl
    · simpa only [if_pos (by decide : Odd 1),if_pos rfl] using c.trans one
    · simpa only [if_neg (by decide : ¬Odd 2),if_neg (by decide : (2:Nat)≠1)] using c.trans two
  · exact ⟨0,Nat.zero_le _,fun j _ => by change _≤if g<U.card ∧ 0<g/2 then _ else _; rw [if_neg ok]; exact old j⟩
end WildSieve
