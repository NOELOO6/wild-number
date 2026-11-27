import FourColors
import TwoCoreCheck

namespace WildSlots
open Finset WildExact WildDeletion WildCuts.OneExtra

/-- Labels of the fixed graph components are verified against actual colored
edges and paths back to their named representatives. -/
structure Trial (n k : Nat) where
  graph : Coloring n k
  fixed : List (EdgeWalk.Edge n)
  point : Three → Fin n
  dest : Three → Fin n
  component : Fin k → Fin n → Fin n

namespace Trial
variable {n k : Nat}
abbrev base (t : Trial n k) := Joined t.graph t.fixed.toFinset

def certified (t : Trial n k) := ∀ c,
  (∀ x : Fin n,(EdgeWalk.run (t.fixed++CoreTest.colored t.graph c) n (2^x.val)).testBit (t.component c x).val=true) ∧
  (∀ e∈t.fixed,t.component c e.1=t.component c e.2) ∧
  ∀ x y : Fin n,x≠y → t.graph.paint x y=c → t.component c x=t.component c y

instance (t : Trial n k) : Decidable t.certified := by
  unfold certified
  infer_instance

theorem comp_iff (t : Trial n k) (cert : t.certified) (c x y) :
    Walk (t.base c) x y ↔ t.component c x=t.component c y := by
  obtain ⟨back,edges,colors⟩ := cert c
  constructor
  · intro path
    induction path with
    | stay => rfl
    | step _ e ih =>
      apply ih.trans
      rcases e with (e|e)|⟨ne,col⟩
      · exact edges _ (List.mem_toFinset.mp e)
      · exact (edges _ (List.mem_toFinset.mp e)).symm
      · exact colors _ _ ne col
  · intro eq
    have one (v) := CoreTest.to_graph t.graph t.fixed c (EdgeWalk.walk_of_seen _ _ _ (back v))
    exact (one x).join (eq ▸ backwards (joined_symm t.graph) (one y))

def reaches (t : Trial n k) := ∀ c x,∃ a : Port,t.component c x=t.component c (port t.point t.dest a)
def entry (t : Trial n k) (c : Fin k) (i j : Three) :=
  ∃ a b : Port,isolated i j a ∧ ¬isolated i j b ∧
    t.component c (port t.point t.dest a)=t.component c (port t.point t.dest b)
instance (t : Trial n k) : Decidable t.reaches := by
  unfold reaches
  infer_instance
instance (i j : Three) (s : Port) : Decidable (isolated i j s) := by cases s <;> exact inferInstanceAs (Decidable (_=_))
instance (t : Trial n k) (c : Fin k) (i j : Three) : Decidable (t.entry c i j) := by
  unfold entry
  infer_instance

def bits (mask : Nat) (i j : Three) := mask.testBit (3*i.val+j.val)

theorem color_iff (t : Trial n k) (cert : t.certified) (vis : t.reaches)
    (ms : Fin k → Nat) (table : ∀ c i j,t.entry c i j ↔ bits (ms c) i j=true)
    (p : Equiv.Perm Three) (c) :
    Connected (Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c) ↔
      ∀ i,bits (ms c) i (p i)=true := by
  let E := fun _ : Unit => t.base c
  have equivalence := assignment_rule E (fun _ {_ _} h => joined_symm t.graph h) t.point t.dest p
  have seen : visible E t.point t.dest := by
    intro _ x
    obtain ⟨a,ha⟩ := vis c x
    exact ⟨a,(t.comp_iff cert c _ _).mpr ha⟩
  have allow (i j) : allowed E t.point t.dest i j ↔ bits (ms c) i j=true := by
    rw [←table]
    constructor
    · intro h
      obtain ⟨a,b,ha,hb,w⟩ := h ()
      exact ⟨a,b,ha,hb,(t.comp_iff cert c _ _).mp w⟩
    · rintro ⟨a,b,ha,hb,eq⟩ _
      exact ⟨a,b,ha,hb,(t.comp_iff cert c _ _).mpr eq⟩
  have rel : Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c=extend (t.base c) t.point t.dest (assign p) :=
    funext₂ (fun x y => propext (joined_draw t.graph _ _ _ _ _ x y))
  rw [rel]
  exact ⟨fun h i => (allow _ _).mp ((equivalence.mp (fun _ => h)).2 i),
    fun h => (equivalence.mpr ⟨seen,fun i => (allow _ _).mpr (h i)⟩) ()⟩

def palette (t : Trial n k) (S : Finset (Fin k)) :=
  ∃ p : Equiv.Perm Three,∀ c∈S,Connected (Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c)

theorem sharp (t : Trial n k) (cert : t.certified) (vis : t.reaches)
    (ms : Fin k → Nat) (table : ∀ c i j,t.entry c i j ↔ bits (ms c) i j=true)
    (S : Finset (Fin k)) (enough : 3≤k)
    (triples : ∀ T : ↥((univ : Finset (Fin k)).powersetCard 3),∃ p : Equiv.Perm Three,
      ∀ c∈T.val,∀ i,bits (ms c) i (p i)=true)
    (no : ∀ p : Equiv.Perm Three,∃ c∈S,∃ i,bits (ms c) i (p i)=false) :
    (∀ T : Finset (Fin k),T.card≤3 → t.palette T) ∧ ¬t.palette S := by
  constructor
  · intro T small
    obtain ⟨U,sub,sz⟩ := exists_superset_card_eq small (by simpa using enough : 3≤Fintype.card (Fin k))
    obtain ⟨p,ok⟩ := triples ⟨U,mem_powersetCard.mpr ⟨subset_univ _,sz⟩⟩
    exact ⟨p,fun c hc => (t.color_iff cert vis ms table p c).mpr (ok c (sub hc))⟩
  · rintro ⟨p,ok⟩
    obtain ⟨c,hc,i,off⟩ := no p
    have on := (t.color_iff cert vis ms table p c).mp (ok c hc) i
    simp_all

end Trial
end WildSlots
