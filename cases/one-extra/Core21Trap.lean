import Core21Data
import TwoCoreCheck
namespace WildCuts.OneExtra.Core21
open Finset WildExact WildDeletion EdgeWalk

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem reaches : MeetsCore graph outside.toFinset coreNine :=
  CoreTest.reaches graph outside coreNine (by native_decide)

private theorem boundaries : ∀ w∈cuts, let S := points w.2
    S.Nonempty ∧ (∃ x : Fin 21,x∉S) ∧
    (∀ e∈outside,(e.1∈S ↔ e.2∈S)) ∧
    ∀ x y : Fin 21,x≠y → paint x y=w.1 → (x∈S ↔ y∈S) := by native_decide

def triples := coreNine.powersetCard 3
def groups (A B : Finset (Fin 21)) : Finset (Finset (Fin 21)) := {A,B,coreNine \ (A∪B)}
def layouts := triples.biUnion fun A => (triples.filter (Disjoint A)).image (groups A)
private theorem checkedBlocks : ∀ P : ↥layouts,∃ w∈cuts,∀ T : ↥P.val,
    T.val⊆points w.2 ∨ Disjoint T.val (points w.2) := by native_decide

private theorem blocked (P) (hp : P∈layouts) : ∃ w∈cuts,∀ T∈P,T⊆points w.2 ∨ Disjoint T (points w.2) := by
  obtain ⟨w,hw,all⟩ := checkedBlocks ⟨P,hp⟩
  exact ⟨w,hw,fun T ht => all ⟨T,ht⟩⟩
theorem total : layouts.card=280 := by native_decide

/-- Any redraw confined to these three triples preserves an explicit cut in
some color. The old edges may also be retained. -/
theorem no_split (P : Finset (Finset (Fin 21))) (hp : P∈layouts) (w : Lines 21)
    (inside : ∀ e∈w,e∈outside ∨ ∃ T∈P,e.1∈T ∧ e.2∈T) : ¬Works graph w := by
  obtain ⟨k,hk,whole⟩ := blocked P hp
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩,old,color⟩ := boundaries k hk
  let S := points k.2
  have wild {u v : Fin 21} (h : (u,v)∈w) : u∈S ↔ v∈S := by
    rcases inside _ h with o|⟨T,ht,uv,vv⟩
    · exact old _ o
    rcases whole T ht with yes|no
    · exact ⟨fun _ => yes vv,fun _ => yes uv⟩
    · exact iff_of_false (disjoint_left.mp no uv) (disjoint_left.mp no vv)
  have stay {u v : Fin 21} (h : Walk (Joined graph w k.1) u v) : u∈S → v∈S := by
    induction h with
    | stay => exact id
    | step _ edge ih =>
      rcases edge with (e|e)|⟨ne,eq⟩
      · exact fun hu => (wild e).mp (ih hu)
      · exact fun hu => (wild e).mpr (ih hu)
      · exact fun hu => (color _ _ ne eq).mp (ih hu)
  intro wins
  exact hy (stay (wins k.1 x y) hx)

/-- The same coloring has the predicted minimum with a different layout. -/
theorem exact : Exact graph 14 :=
  CoreTest.winner graph (by decide) winner (by native_decide) (by native_decide) (by native_decide)

#print axioms reaches
#print axioms no_split
#print axioms exact
end WildCuts.OneExtra.Core21
