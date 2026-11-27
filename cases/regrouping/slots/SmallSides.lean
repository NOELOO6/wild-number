import SlotCuts

namespace WildSlots
open Finset WildDeletion WildExact

/-- In a temporary graph all links within the two specified sides are available. -/
def splitLinks {I : Type} (A B : Finset I) (i j : I) := i∈A ↔ j∈B

/-- For a proposed permutation it suffices to test subsets of at most half
the slots. The opposite side defines exactly the same temporary graph. -/
theorem smaller_sides {I V C : Type} [Fintype I] (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : I → V) (p : Equiv.Perm I) :
    passes E u v (assign p) ↔
    ∀ A : Finset I,A.card≤Fintype.card I/2 → passes E u v (splitLinks A (A.map p.toEmbedding)) := by
  classical
  have mapMem (A : Finset I) (j) : j∈A.map p.toEmbedding ↔ p.symm j∈A := by simp
  constructor
  · intro yes A _
    exact passes_mono (fun i j (eq : p i=j) => by simp [splitLinks,mapMem,←eq]) yes
  · intro yes
    apply pass_from_tests E sym u v p (fun A : {A : Finset I // A.card≤Fintype.card I/2} =>
      splitLinks A.val (A.val.map p.toEmbedding)) _ (fun A => yes A.val A.property)
    intro f
    let A := univ.filter (fun i => f i=true)
    have inA (i) : i∈A ↔ f i=true := by simp [A]
    by_cases small : A.card≤Fintype.card I/2
    · refine ⟨⟨A,small⟩,?_⟩
      intro i j same
      exact Bool.eq_iff_iff.mpr ((inA i).symm.trans (same.trans ((mapMem _ _).trans (inA _))))
    · have size : Aᶜ.card≤Fintype.card I/2 := by rw [card_compl]; omega
      refine ⟨⟨Aᶜ,size⟩,?_⟩
      intro i j same
      have neg : i∉A ↔ p.symm j∉A := by
        simpa only [splitLinks,mapMem,mem_compl] using same
      exact Bool.eq_iff_iff.mpr ((inA _).symm.trans ((not_iff_not.mp neg).trans (inA _)))

/-- Temporary singleton test used by the concrete five-point examples. -/
def oneCell {I : Type} (i j a b : I) := a=i ↔ b=j

/-- With five slots the complete test consists of the five singletons and ten
pairs prescribed by the proposed assignment. -/
theorem five_sides {V C : Type} (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : Fin 5 → V) (p : Equiv.Perm (Fin 5)) :
    passes E u v (assign p) ↔
    (∀ i,passes E u v (oneCell i (p i))) ∧
    (∀ A : Finset (Fin 5),A.card=2 → passes E u v (splitLinks A (A.map p.toEmbedding))) := by
  classical
  have one (i : Fin 5) : splitLinks {i} (({i} : Finset _).map p.toEmbedding)=oneCell i (p i) := by
    funext a b
    simp [splitLinks,oneCell]
  constructor
  · intro win
    have cuts := (smaller_sides E sym u v p).mp win
    exact ⟨fun i => one i ▸ cuts {i} (by simp),fun A pair => cuts A (by simp [pair])⟩
  · rintro ⟨singles,pairs⟩
    apply (smaller_sides E sym u v p).mpr
    intro A small
    have bound : A.card≤2 := by simpa using small
    by_cases z : A.card=0
    · have empty := card_eq_zero.mp z
      subst A
      exact passes_mono (P:=oneCell 0 (p 0)) (fun i j _ => by simp [splitLinks]) (singles 0)
    · by_cases o : A.card=1
      · obtain ⟨i,rfl⟩ := card_eq_one.mp o
        rw [one]; exact singles i
      · exact pairs A (by omega)

#print axioms five_sides
end WildSlots
