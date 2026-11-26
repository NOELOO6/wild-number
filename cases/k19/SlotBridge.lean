import PlacementCertificate
namespace K19Placement
/-- A component holds actual unused slots. Labeling every slot by the index of
its component gives a concrete list whose projection is the abstract ticket list. -/
def grouped {S : Type} (s : Shape) (holes : Nat → List S) :=
  s.zipIdx.flatMap fun (_,b) => (holes b).map (fun t => (t,b))

private theorem repeated_map {S T : Type} (xs : List S) (v : T) :
    xs.map (fun _ => v) = List.replicate xs.length v := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih, List.replicate_succ]

theorem label_the_slots {S : Type} (s : Shape) (holes : Nat → List S) (a : Option Nat)
    (sizes : ∀ e ∈ s.zipIdx, (holes e.2).length = free e.1) :
    ((grouped s holes).map (fun q => move s a q.2)) = tickets s a := by
  unfold grouped tickets
  rw [List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro e he
  rw [List.map_map]
  rw [show ((fun (q : S × Nat) => move s a q.2) ∘ fun t : S => (t,e.2)) =
        (fun _ => move s a e.2) from rfl, repeated_map, sizes e he]

/-- Obtain the game transition from the ordinary slot inventory. Each color
can put the same children in a different order. The two hypotheses say that
the component buckets contain precisely those children and describe their
single-edge updates. -/
theorem outcomes_from_slots {X S : Type} (xs : List X) (s : Shape) (holes : Nat → List S)
    (loc : X → S × Nat) (after : X → Shape) (a : Option Nat)
    (sizes : ∀ e ∈ s.zipIdx, (holes e.2).length = free e.1)
    (inventory : (xs.map loc).Perm (grouped s holes))
    (actualMove : ∀ x ∈ xs, after x = move s a (loc x).2) :
    (xs.map after).Perm (tickets s a) := by
  have hp := inventory.map (fun (q : S × Nat) => move s a q.2)
  rw [label_the_slots s holes a sizes, List.map_map] at hp
  have eq : xs.map after = xs.map (fun x => move s a (loc x).2) := by
    apply List.map_congr_left
    exact actualMove
  rw [eq]
  exact hp
#print axioms outcomes_from_slots
end K19Placement
