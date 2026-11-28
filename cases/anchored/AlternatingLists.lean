import AlternatingOrbits
import CycleLists
import LocalFrames
import MatchingModel

namespace WildAnchor.Alternating
open Function Finset WildExact

/-- Canonical successor in consecutive cycles of the listed lengths. -/
def successor : List Nat → Nat → Nat
  | [],i => i
  | l::ls,i => if i<l then (i+1)%l else l+successor ls (i-l)

theorem successor_lt (cs : List Nat) (i : Nat) (h : i<cs.sum) : successor cs i<cs.sum := by
  induction cs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.sum_cons] at h ⊢
    simp only [successor];split
    · have := Nat.mod_lt (i+1) (by omega : 0<x); omega
    · have := ih (i-x) (by omega);omega

namespace Pairing
variable {V : Type} [Fintype V] [DecidableEq V] (P : Pairing V)

private def Listing (U : Finset V) (cs : List Nat) (number : Nat → V) : Prop :=
  (∀ v∈U,∃ i<cs.sum,v=number i ∨ v=P.first (number i)) ∧
    ∀ i<cs.sum,P.second (number i)=P.first (number (successor cs i))

private theorem enumerate (U : Finset V) [Nonempty V] (lo : Nat)
    (bottom : ∀ x∈U,lo≤P.period x) (a : ∀ x∈U,P.first x∈U) (b : ∀ x∈U,P.second x∈U) :
    ∃ cs,2*cs.sum=U.card ∧ (∀ l∈cs,lo≤l) ∧ cs.Pairwise (·≤·) ∧ ∃ number,P.Listing U cs number := by
  classical
  induction U using Finset.strongInductionOn generalizing lo
  rename_i U ih
  rcases U.eq_empty_or_nonempty with rfl|non
  · exact ⟨[],by simp,by simp,by simp,fun _ => Classical.choice inferInstance,by simp [Listing]⟩
  obtain ⟨x,hx,least⟩ := exists_min_image U P.period non
  let p := P.period x
  let C := P.component x
  let R := U \ C
  have pos := P.period_pos x
  have root : x∈C := (P.mem_component ..).mpr ⟨0,pos,Or.inl rfl⟩
  have sub : C⊆U := P.component_subset U x hx a b
  have strict : R⊂U := ssubset_iff_of_subset sdiff_subset |>.mpr ⟨x,hx,fun h => (mem_sdiff.mp h).2 root⟩
  have closed := P.component_closed x
  have outside {f : V → V} (inv : Involutive f) (outer : ∀ y∈U,f y∈U) (inner : ∀ y∈C,f y∈C) :
      ∀ y∈R,f y∈R := by
    intro y hy
    obtain ⟨yu,yc⟩ := mem_sdiff.mp hy
    exact mem_sdiff.mpr ⟨outer _ yu,fun h => yc (inv y ▸ inner _ h)⟩
  obtain ⟨cs,card,low,ordered,f,cover,link⟩ := ih R strict p
    (fun y hy => least _ (mem_sdiff.mp hy).1) (outside P.first_inv a closed.1) (outside P.second_inv b closed.2)
  have nc : C.card=2*p := P.component_card x
  have nr : R.card=U.card-C.card := card_sdiff sub
  have le := card_le_card sub
  let num (i : Nat) := if i<p then P.point x i else f (i-p)
  refine ⟨p::cs,by simp only [List.sum_cons];omega,?_,List.pairwise_cons.mpr ⟨low,ordered⟩,num,?_,?_⟩
  · intro l hl
    rcases List.mem_cons.mp hl with rfl|hl
    · exact bottom x hx
    · exact (bottom x hx).trans (low l hl)
  · intro y hy
    by_cases yc : y∈C
    · obtain ⟨i,small,e⟩ := (P.mem_component ..).mp yc
      change i<p at small
      exact ⟨i,by simp only [List.sum_cons];omega,by simpa only [num,if_pos small] using e⟩
    · obtain ⟨i,small,e⟩ := cover y (mem_sdiff.mpr ⟨hy,yc⟩)
      exact ⟨p+i,by simpa only [List.sum_cons,Nat.add_lt_add_iff_left] using small,by
        simpa only [num,if_neg (by omega : ¬p+i<p),Nat.add_sub_cancel_left] using e⟩
  · intro i hi
    simp only [List.sum_cons] at hi
    by_cases il : i<p
    · have lt : (i+1)%p<p := Nat.mod_lt _ pos
      simpa only [num,successor,if_pos il,if_pos lt] using P.advance x i
    · have hnext : ¬p+successor cs (i-p)<p := by omega
      simpa only [num,successor,if_neg il,if_neg hnext,Nat.add_sub_cancel_left] using link (i-p) (by omega)

/-- Each pair of matchings admits a common enumeration by alternating
cycles, sorted by length. Its only graph data are the two involutions. -/
theorem sorted_cycles {m : Nat} [Nonempty V] (size : Fintype.card V=2*m) (lo : Nat)
    (bottom : ∀ x,lo≤P.period x) :
    ∃ cs,OrderedCycles m lo cs ∧ ∃ w : Point m ≃ V,
      (∀ i,P.first (w (i,false))=w (i,true)) ∧
      ∀ i j : Fin m,j.val=successor cs i.val → P.second (w (i,false))=w (j,true) := by
  obtain ⟨cs,card,low,order,num,cover,link⟩ := P.enumerate univ lo (fun x _ => bottom x)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  rw [card_univ,size] at card
  have total : cs.sum=m := by omega
  let w (z : Point m) := if z.2 then P.first (num z.1.val) else num z.1.val
  have onto : Surjective w := by
    intro v
    obtain ⟨i,hi,e|e⟩ := cover v (mem_univ _)
    · exact ⟨(⟨i,total ▸ hi⟩,false),e.symm⟩
    · exact ⟨(⟨i,total ▸ hi⟩,true),e.symm⟩
  have sameSize : Fintype.card (Point m)=Fintype.card V := by simp [size,Fintype.card_prod,Nat.mul_comm]
  let e := Equiv.ofBijective w ((Fintype.bijective_iff_surjective_and_card w).mpr ⟨onto,sameSize⟩)
  refine ⟨cs,⟨total,low,order⟩,e,fun _ => rfl,?_⟩
  intro i j eq
  change P.second (num i.val)=P.first (num j.val)
  exact eq ▸ link i.val (total ▸ i.isLt)

end Pairing
end WildAnchor.Alternating
