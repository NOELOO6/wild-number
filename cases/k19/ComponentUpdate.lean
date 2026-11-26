import SlotBridge
namespace K19Placement
/-- A concrete component has named empty slots and named unplaced partners. -/
structure Cell (S A : Type) where
  holes : List S
  waitingFor : List A

def code {S A} (b : Cell S A) := 32*b.holes.length + b.waitingFor.length

theorem read_code {S A} (b : Cell S A) (hb : b.waitingFor.length < 32) :
    free (code b) = b.holes.length ∧ waiting (code b) = b.waitingFor.length := by
  unfold free waiting code
  omega

def openEdge {S A} [BEq S] (b : Cell S A) (slot : S) (mate : A) : Cell S A :=
  ⟨b.holes.erase slot,mate::b.waitingFor⟩
def closeInside {S A} [BEq S] [BEq A] (b : Cell S A) (slot : S) (vertex : A) : Cell S A :=
  ⟨b.holes.erase slot,b.waitingFor.erase vertex⟩
def closeAcross {S A} [BEq S] [BEq A] (b old : Cell S A) (slot : S) (vertex : A) : Cell S A :=
  ⟨b.holes.erase slot ++ old.holes,b.waitingFor ++ old.waitingFor.erase vertex⟩

theorem opening_count {S A} [DecidableEq S] (b : Cell S A) (slot : S) (mate : A)
    (hs : slot ∈ b.holes) (hb : b.waitingFor.length < 32) :
    code (openEdge b slot mate) = 32*(free (code b)-1)+(waiting (code b)+1) := by
  obtain ⟨f,w⟩ := read_code b hb
  rw [f,w]
  simp [code,openEdge,List.length_erase_of_mem hs]

theorem inside_count {S A} [DecidableEq S] [DecidableEq A] (b : Cell S A) (slot : S) (v : A)
    (hs : slot ∈ b.holes) (hv : v ∈ b.waitingFor) (hb : b.waitingFor.length < 32) :
    code (closeInside b slot v) = 32*(free (code b)-1)+(waiting (code b)-1) := by
  obtain ⟨f,w⟩ := read_code b hb
  rw [f,w]
  simp [code,closeInside,List.length_erase_of_mem hs,List.length_erase_of_mem hv]

theorem across_count {S A} [DecidableEq S] [DecidableEq A] (b old : Cell S A) (slot : S) (v : A)
    (hs : slot ∈ b.holes) (hv : v ∈ old.waitingFor)
    (hb : b.waitingFor.length < 32) (ho : old.waitingFor.length < 32) :
    code (closeAcross b old slot v) =
      32*(free (code b)+free (code old)-1)+(waiting (code b)+waiting (code old)-1) := by
  obtain ⟨f,w⟩ := read_code b hb
  obtain ⟨g,z⟩ := read_code old ho
  rw [f,w,g,z]
  simp only [code,closeAcross,List.length_append,List.length_erase_of_mem hs,List.length_erase_of_mem hv]
  have hp := List.length_pos_of_mem hs
  have hq := List.length_pos_of_mem hv
  omega

/-- When a point is absent from the waiting list there is room to open an
edge. This uses the ordinary partition into waiting and unpaired points. -/
theorem room_to_open {A : Type} {v : A} {unplaced pending unseen : List A}
    (cover : unplaced.Perm (pending++unseen)) (hv : v ∈ unplaced) (hn : v ∉ pending) :
    pending.length < unplaced.length := by
  have h := cover.length_eq
  rw [List.length_append] at h
  have hs := List.mem_append.mp (cover.mem_iff.mp hv)
  have pos := List.length_pos_of_mem (hs.resolve_left hn)
  omega
#print axioms across_count
#print axioms room_to_open
end K19Placement
