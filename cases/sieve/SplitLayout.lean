import FrozenLayout
namespace WildSieve
open Finset

def ordinaryD {A : Type} [DecidableEq A] (r : A) : List (Finset A) := [∅,{r}]

def lateD {A : Type} [DecidableEq A] (B : Finset A) (r : A) (f t j : Nat) :=
  if j∈shortLevels then (if 0<f ∧ 2*j<t then [B.erase r,B] else []) else choices B r f t j

def lateWidths (f t j : Nat) :=
  if j∈shortLevels then (if 0<f ∧ 2*j<t then [f,f+1] else []) else widths f t j

def shortDegree (n f t u j : Nat) := ([0,1].map
  (fun d => improvedDegree n (3*t) (f+1) d (3*j) u)).sum

def lateCount (n f t j : Nat) := ((lateWidths f t j).map
  (fun d => totalFor n (3*t) (f+1) d (3*j) (3*t))).sum

def SplitCertWith (n f t : Nat) (degree : Nat → Nat → Nat) (h : Nat → ℚ) :=
  (∀ u≤3*t,0<h u) ∧ (∀ u,0<u → u≤3*t →
    ∑ j∈shortLevels,(degree u j : ℚ)*(sealWeight t j*h (u-3*j)) ≤ h (u-1)-h u) ∧
  (∑ j∈shortLevels∪longLevels t,(lateCount n f t j : ℚ)*(sealWeight t j*h (3*t-3*j))) < h (3*t)

abbrev SplitCert (n f t : Nat) := SplitCertWith n f t (shortDegree n f t)

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

noncomputable def ordinaryScopes (F : Factor A C) (B : Finset A) (r : A) (j : Nat) :=
  gather (fun D => pullSides F B D (3*j)) (ordinaryD r)

theorem ordinary_degree (F : Factor A C) (B : Finset A) (r : A) (f t : Nat)
    (hr : r∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (U : Finset (Free B)) (z : Free B) (zu : z∈U) (j : Nat) :
    (active (ordinaryScopes F B r j) U z).card≤shortDegree (Fintype.card C) f t U.card j := by
  classical
  let d (D) := active (pullSides F B D (3*j)) U z
  have sub : active (ordinaryScopes F B r j) U z ⊆ gather d (ordinaryD r) := by
    intro X hx
    obtain ⟨xb,xu⟩ := mem_filter.mp hx
    obtain ⟨D,dl,xd⟩ := (mem_gather _ _ X).mp xb
    exact (mem_gather _ _ _).mpr ⟨D,dl,mem_filter.mpr ⟨xd,xu⟩⟩
  have b := bound_gather d (ordinaryD r) (fun D => improvedDegree (Fintype.card C) Bᶜ.card B.card D.card (3*j) U.card)
    (fun D hd => pull_degree F B D _ U z zu rain (choices_sub B r hr f t j D (List.mem_append_left _ hd)))
  exact (card_le_card sub).trans (by simpa [shortDegree,ordinaryD,ws,bs] using b)

/-- The local sieve only charges cuts away from the frozen group. Cuts that
contain that group enter the final sum at their original number of triples. -/
theorem frozen_split_with (F : Factor A C) (B : Finset A) (r : A) (f t : Nat)
    (hr : r∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (degree : Nat → Nat → Nat)
    (localBound : ∀ (U : Finset (Free B)) (z : Free B),z∈U → ∀ j∈shortLevels,
      (active (ordinaryScopes F B r j) U z).card≤degree U.card j)
    (h : Nat → ℚ) (cert : SplitCertWith (Fintype.card C) f t degree h) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j∈shortLevels∪longLevels t,∀ X∈badScopes F B r f t j,
      L∉sealEvent X := by
  classical
  let scopes (j : Nat) (L : List (Finset A)) := gather (fun D => pullSides F B D (3*j)) L
  have size (j L X) (hx : X∈scopes j L) : X.card=3*j := by
    obtain ⟨D,_,xd⟩ := (mem_gather _ _ X).mp hx
    exact (pull_mem.mp xd).1
  have subsetLate (j D) (hd : D∈lateD B r f t j) : D∈choices B r f t j := by
    by_cases sh : j∈shortLevels
    · simpa only [lateD,if_pos sh] using (show D∈choices B r f t j from
        List.mem_append_right _ (by simpa only [lateD,if_pos sh] using hd))
    · simpa only [lateD,if_neg sh] using hd
  have widthsLate (j) : (lateD B r f t j).map Finset.card=lateWidths f t j := by
    by_cases sh : j∈shortLevels
    · by_cases add : 0<f ∧ 2*j<t <;> simp [lateD,lateWidths,sh,add,card_erase_of_mem hr,bs]
    · simpa only [lateD,lateWidths,if_neg sh] using width_eq B r hr f t j bs
  obtain ⟨L,early,late⟩ := partition_split t ((Fintype.card_coe Bᶜ).trans ws)
    shortLevels (shortLevels∪longLevels t) (fun j => scopes j (ordinaryD r))
    (fun j => scopes j (lateD B r f t j)) (fun j _ => size j _) (fun j _ => size j _)
    (fun j hj => by simp [shortLevels] at hj; omega)
    degree (lateCount (Fintype.card C) f t) localBound
    (by
      intro j _
      have b := bound_gather (fun D => pullSides F B D (3*j)) (lateD B r f t j)
        (fun D => totalFor (Fintype.card C) Bᶜ.card B.card D.card (3*j) Bᶜ.card)
        (fun D hd => pull_total F B D _ rain (choices_sub B r hr f t j D (subsetLate j D hd)))
      unfold lateCount
      rw [← widthsLate j,List.map_map]
      simpa [scopes,ws,bs,Function.comp_def] using b) h cert.1 cert.2.1 cert.2.2
  refine ⟨L,fun j hj X hx => ?_⟩
  obtain ⟨D,hd,xd⟩ := (mem_gather _ _ X).mp hx
  by_cases sh : j∈shortLevels
  · rcases List.mem_append.mp hd with a|b
    · exact early j sh X ((mem_gather _ _ _).mpr ⟨D,a,xd⟩)
    · exact late j hj X ((mem_gather _ _ _).mpr ⟨D,by simpa only [lateD,if_pos sh] using b,xd⟩)
  · exact late j hj X ((mem_gather _ _ _).mpr ⟨D,by simpa only [lateD,if_neg sh] using hd,xd⟩)

theorem frozen_split (F : Factor A C) (B : Finset A) (r : A) (f t : Nat)
    (hr : r∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (h : Nat → ℚ) (cert : SplitCert (Fintype.card C) f t h) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j∈shortLevels∪longLevels t,∀ X∈badScopes F B r f t j,
      L∉sealEvent X := frozen_split_with F B r f t hr bs ws rain (shortDegree (Fintype.card C) f t)
  (fun U z zu j _ => ordinary_degree F B r f t hr bs ws rain U z zu j) h cert

end WildSieve
