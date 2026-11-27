import CoreBudget
namespace WildCuts.OneExtra
open Finset WildExact WildDeletion

/-- Index by the number of connected pieces meeting the core. -/
def lossCap (s pieces : Nat) : Nat :=
  let row := match s with
    | 6 => #[0,0,1,1,2,4,10]
    | 7 => #[0,0,1,2,3,7,15,35]
    | 8 => #[0,0,1,2,4,9,19,41,91]
    | _ => #[]
  row[pieces]?.getD 0

/-- Consecutive vertices between two breaks belong to the same piece. -/
def consistent {s : Nat} (D A : Finset (Fin s)) := ∀ i j : Fin s,
  i.val+1=j.val → j∉D → (i∈A ↔ j∈A)
instance {s : Nat} (D A : Finset (Fin s)) : Decidable (consistent D A) :=
  inferInstanceAs (Decidable (∀ i j : Fin s,i.val+1=j.val → j∉D → (i∈A ↔ j∈A)))

def permitted {s : Nat} (z : Fin s) (D : Finset (Fin s)) :=
  (choices univ z).filter (consistent D)

private def checked (s : Nat) (z : Fin s) := ∀ D : Finset (Fin s),
    z∉D → (permitted z D).card≤lossCap s (D.card+1)

private instance {s : Nat} (z : Fin s) : Decidable (checked s z) :=
  inferInstanceAs (Decidable (∀ D : Finset (Fin s),z∉D → (permitted z D).card≤lossCap s (D.card+1)))

set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem six : checked 6 0 := by native_decide
private theorem seven : checked 7 0 := by native_decide
private theorem eight : checked 8 0 := by native_decide

/-- Each color may number the core in its own order, starting at the common
root. A run between breaks only requires paths in that color and the exterior.
Its vertices need not be adjacent in the original complete graph. -/
theorem profile_budget {n k s limit : Nat} (pos : 0<k) (small : s=6 ∨ s=7 ∨ s=8)
    (g : Coloring n k) (w : Lines n) (R : Finset (Fin n)) (r : Fin n) (hr : r∈R)
    (legal : Legal w) (reach : MeetsCore g w R) (label : Fin k → Fin s ≃ ↥R)
    (z : Fin s) (zero : z.val=0) (root : ∀ c,(label c z).val=r)
    (D : Fin k → Finset (Fin s)) (start : ∀ c,z∉D c)
    (runs : ∀ c (i j : Fin s),i.val+1=j.val → j∉D c →
      Walk (Joined g w c) (label c i).val (label c j).val)
    (count : (∑ c,lossCap s ((D c).card+1))<splitCount s)
    (budget : w.card+(R.card-2)≤limit) : Upper g limit := by
  classical
  have sz : R.card=s := by simpa using (Fintype.card_congr (label ⟨0,pos⟩)).symm
  apply affordable pos g w R r hr legal reach (fun c => lossCap s ((D c).card+1)) _ (sz ▸ count) budget
  intro c
  let bad := blocked g w R r c
  let code (A : Finset (Fin n)) := univ.filter (fun j => (label c j).val∈A)
  have size {A} (sub : A⊆R) : (code A).card=A.card := by
    apply card_bij (fun j _ => (label c j).val)
    · exact fun _ hj => (mem_filter.mp hj).2
    · exact fun _ _ _ _ eq => (label c).injective (Subtype.ext eq)
    · intro x hx
      exact ⟨(label c).symm ⟨x,sub hx⟩,mem_filter.mpr ⟨mem_univ _,by simpa using hx⟩,by simp⟩
  have le := card_le_card_of_injOn (s:=bad) (t:=permitted z (D c)) code (by
    intro A ha
    obtain ⟨base,no⟩ := mem_filter.mp ha
    obtain ⟨sub,out,_⟩ := side_info base
    have cut := (mem_filter.mp base).2
    apply mem_filter.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (fun j hj => mem_erase.mpr ⟨?_,mem_univ _⟩),?_⟩
      · intro jz
        have h := (mem_filter.mp hj).2
        exact out ((jz ▸ root c) ▸ h)
      · simpa only [size sub,card_univ,Fintype.card_fin,←sz] using cut
    · intro i j ij kept
      let x := (label c i).val
      let y := (label c j).val
      have hx : x∈R := (label c i).property
      have hy : y∈R := (label c j).property
      have walk := runs c i j ij kept
      simp only [code,mem_filter,mem_univ,true_and]
      exact ⟨fun hi => by_contra (fun hj => no ⟨x,hi,y,mem_sdiff.mpr ⟨hy,hj⟩,walk⟩),
        fun hj => by_contra (fun hi => no ⟨y,hj,x,mem_sdiff.mpr ⟨hx,hi⟩,backwards (joined_symm g) walk⟩)⟩)
    (by
      intro A ha B hb eq
      change code A=code B at eq
      have sa := (side_info (mem_filter.mp ha).1).1
      have sb := (side_info (mem_filter.mp hb).1).1
      ext x
      by_cases hx : x∈R
      · let j := (label c).symm ⟨x,hx⟩
        simpa [code,j] using (show j∈code A ↔ j∈code B by rw [eq])
      · exact iff_of_false (fun h => hx (sa h)) (fun h => hx (sb h)))
  apply le.trans
  have cert : checked s z := by
    rcases small with rfl|rfl|rfl
    · exact (show z=(0 : Fin 6) from Fin.ext zero) ▸ six
    · exact (show z=(0 : Fin 7) from Fin.ext zero) ▸ seven
    · exact (show z=(0 : Fin 8) from Fin.ext zero) ▸ eight
  exact cert (D c) (start c)

#print axioms profile_budget
end WildCuts.OneExtra
