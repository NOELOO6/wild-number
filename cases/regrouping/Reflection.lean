import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Filter

namespace WildExact.Reflection
open Finset

/-- The three offsets occupy different residue classes modulo three. -/
def Port (a : Nat) := a=0 ∨ a=4 ∨ a=5
private theorem same_port {a b : Nat} (pa : Port a) (pb : Port b) (h : a%3=b%3) : a=b := by
  rcases pa with rfl|rfl|rfl <;> rcases pb with rfl|rfl|rfl <;> omega

/-- No nonempty collection of these translated triples is symmetric under
ordinary reflection on the integer line. -/
private theorem linear_impossible (I : Finset Nat) (ne : I.Nonempty) (k : Nat)
    (reflect : ∀ i∈I, ∀ a,Port a → ∃ j∈I, ∃ b,Port b ∧ (3*i+a)+(3*j+b)=k) : False := by
  let l := I.min' ne
  let h := I.max' ne
  have il : l∈I := min'_mem _ _
  have ih : h∈I := max'_mem _ _
  obtain ⟨i,ie,a,pa,ea⟩ := reflect l il 0 (Or.inl rfl)
  obtain ⟨j,je,b,pb,eb⟩ := reflect h ih 5 (Or.inr (Or.inr rfl))
  have im : i≤h := le_max' _ _ ie
  have jm : l≤j := min'_le _ _ je
  have ab : a≤5 := by rcases pa with rfl|rfl|rfl <;> decide
  have key : k=3*l+3*h+5 := by omega
  obtain ⟨v,ve,d,pd,ed⟩ := reflect h ih 4 (Or.inr (Or.inl rfl))
  have vm : l≤v := min'_le _ _ ve
  rcases pd with rfl|rfl|rfl <;> omega

private theorem count_le {A B : Finset Nat} {a b k : Nat}
    (hit : ∀ i∈A,∃ j∈B,(3*i+a)+(3*j+b)=k) : A.card≤B.card := by
  apply card_le_card_of_injOn (fun i => (k-(3*i+a)-b)/3)
  · intro i hi
    obtain ⟨j,hj,eq⟩ := hit i hi
    rwa [show (k-(3*i+a)-b)/3=j by omega]
  · intro i hi j hj same
    obtain ⟨v,_,ev⟩ := hit i hi
    obtain ⟨w,_,ew⟩ := hit j hj
    dsimp at same
    omega

/-- A nonempty union of the triples {3i,3i+4,3i+5} cannot be invariant
under a reflection of a cycle of order coprime to three. -/
theorem no_cyclic_reflection (n c : Nat) (cop : n%3≠0) (I : Finset Nat) (ne : I.Nonempty)
    (fits : ∀ i∈I,3*i+5<n)
    (reflect : ∀ i∈I, ∀ a,Port a → ∃ j∈I, ∃ b,Port b ∧
      (3*i+a)+(3*j+b)=(if 3*i+a≤c then c else n+c)) : False := by
  let low (a : Nat) := I.filter (fun i => 3*i+a≤c)
  let high (a : Nat) := I.filter (fun i => c<3*i+a)
  have lowHits (a b) (pa : Port a) (pb : Port b) (modEq : (a+b)%3=c%3) :
      ∀ i∈low a,∃ j∈low b,(3*i+a)+(3*j+b)=c := by
    intro i hi
    obtain ⟨ii,le⟩ := mem_filter.mp hi
    obtain ⟨j,ji,d,pd,eq⟩ := reflect i ii a pa
    rw [if_pos le] at eq
    have db := same_port pd pb (by omega)
    subst d
    exact ⟨j,mem_filter.mpr ⟨ji,by omega⟩,eq⟩
  have highHits (a b) (pa : Port a) (pb : Port b) (modEq : (a+b)%3=(n+c)%3) :
      ∀ i∈high a,∃ j∈high b,(3*i+a)+(3*j+b)=n+c := by
    intro i hi
    obtain ⟨ii,gt⟩ := mem_filter.mp hi
    have bound := fits i ii
    have ac : a≤5 := by rcases pa with rfl|rfl|rfl <;> decide
    obtain ⟨j,ji,d,pd,eq⟩ := reflect i ii a pa
    rw [if_neg (by omega)] at eq
    have db := same_port pd pb (by omega)
    subst d
    exact ⟨j,mem_filter.mpr ⟨ji,by omega⟩,eq⟩
  have total (a) : (low a).card+(high a).card=I.card := by
    have hh : high a=I \ low a := by
      ext i
      by_cases ii : i∈I <;> simp [high,low,ii]
    rw [hh,Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have coupled (a b) (pa : Port a) (pb : Port b)
      (eq : (a+b)%3=c%3 ∨ (a+b)%3=(n+c)%3) : (low a).card=(low b).card := by
    rcases eq with lower|higher
    · exact Nat.le_antisymm (count_le (lowHits a b pa pb lower))
        (count_le (lowHits b a pb pa (by rwa [Nat.add_comm])))
    · have x := count_le (highHits a b pa pb higher)
      have y := count_le (highHits b a pb pa (by rwa [Nat.add_comm]))
      have ta := total a
      have tb := total b
      omega
  have p0 : Port 0 := Or.inl rfl
  have p4 : Port 4 := Or.inr (Or.inl rfl)
  have p5 : Port 5 := Or.inr (Or.inr rfl)
  have x := coupled 0 4 p0 p4
  have y := coupled 0 5 p0 p5
  have z := coupled 4 5 p4 p5
  have size : (low 0).card=(low 5).card := by omega
  have sub : low 5⊆low 0 := fun i hi => mem_filter.mpr ⟨(mem_filter.mp hi).1,by have := (mem_filter.mp hi).2; omega⟩
  have same : low 5=low 0 := eq_of_subset_of_card_le sub size.le
  have unsplit (i) (ii : i∈I) (a) (pa : Port a) : 3*i+a≤c ↔ 3*i≤c := by
    have ab : a≤5 := by rcases pa with rfl|rfl|rfl <;> decide
    refine ⟨by omega,fun le => ?_⟩
    have hm : i∈low 0 := mem_filter.mpr ⟨ii,by omega⟩
    rw [← same] at hm
    have last := (mem_filter.mp hm).2
    omega
  obtain ⟨seed,si⟩ := ne
  let left := decide (3*seed≤c)
  let J := I.filter (fun i => decide (3*i≤c)=left)
  have seedJ : seed∈J := mem_filter.mpr ⟨si,rfl⟩
  apply linear_impossible J ⟨seed,seedJ⟩ (if left then c else n+c)
  intro i hi a pa
  obtain ⟨ii,zone⟩ := mem_filter.mp hi
  obtain ⟨j,ji,b,pb,eq⟩ := reflect i ii a pa
  have ua := unsplit i ii a pa
  have ub := unsplit j ji b pb
  have fit := fits i ii
  have ab : a≤5 := by rcases pa with rfl|rfl|rfl <;> decide
  by_cases side : 3*i≤c
  · have l : left=true := by simpa [side] using zone.symm
    rw [if_pos (ua.mpr side)] at eq
    have js : 3*j≤c := by omega
    exact ⟨j,mem_filter.mpr ⟨ji,by simp [js,l]⟩,b,pb,by simpa [l] using eq⟩
  · have l : left=false := by simpa [side] using zone.symm
    rw [if_neg (fun h => side (ua.mp h))] at eq
    have js : ¬3*j≤c := fun h => by have := ub.mpr h; omega
    exact ⟨j,mem_filter.mpr ⟨ji,by simp [js,l]⟩,b,pb,by simpa [l] using eq⟩

#print axioms no_cyclic_reflection
end WildExact.Reflection
