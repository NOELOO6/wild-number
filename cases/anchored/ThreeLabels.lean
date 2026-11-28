import PairPlacement

namespace WildAnchor
open Finset

abbrev Label := Fin 3
abbrev Colors3 (I : Type) := I → Label × Label

/-- The three diagonal pairs, followed by the three unordered mixed pairs. -/
def pairKind (x : Label × Label) : Fin 6 :=
  if x.1=x.2 then ⟨x.1.val,by omega⟩
  else if x.1+x.2=1 then 3 else if x.1+x.2=2 then 4 else 5

private theorem same_kind : ∀ x y : Label × Label, pairKind x=pairKind y →
    x=y ∨ x.swap=y := by decide

def turnPair (b : Bool) (x : Label × Label) := if b then x.swap else x

def fitsThree {I : Type} (q : Shuffle I) (s t : Colors3 I) :=
  ∀ i,turnPair (q.2 i) (s i)=t (q.1 i)

variable {I : Type} [Fintype I] [DecidableEq I]
instance (q : Shuffle I) (s t : Colors3 I) : Decidable (fitsThree q s t) :=
  inferInstanceAs (Decidable (∀ _,_))

def sizeThree (s : Colors3 I) (j : Fin 6) := (univ.filter fun i => pairKind (s i)=j).card
def diagonal (s : Colors3 I) := (univ.filter fun i => (s i).1=(s i).2).card

def priceThree (s t : Colors3 I) : Nat := if ∀ j,sizeThree s j=sizeThree t j then
  (∏ j,(sizeThree s j).factorial)*2^(diagonal s) else 0

/-- A lower bound on the number of anchor shuffles carrying two specified,
disjoint cuts simultaneously. Choose a bijection for each unordered pair
of labels and a free orientation for each equal-label anchor edge. -/
theorem three_price_le (s t : Colors3 I) :
    priceThree s t ≤ (univ.filter fun q : Shuffle I => fitsThree q s t).card := by
  classical
  by_cases eq : ∀ j,sizeThree s j=sizeThree t j
  · let K (a : Colors3 I) (j : Fin 6) := {i : I // pairKind (a i)=j}
    let R := {i : I // (s i).1=(s i).2}
    let Data := (∀ j,K s j ≃ K t j) × (R → Bool)
    let permute (v : Data) : Equiv.Perm I := Equiv.ofFiberEquiv v.1
    have classEq (v : Data) (i : I) : pairKind (t (permute v i))=pairKind (s i) :=
      (v.1 (pairKind (s i)) ⟨i,rfl⟩).property
    let orient (v : Data) (i : I) : Bool := if h : (s i).1=(s i).2 then v.2 ⟨i,h⟩
      else decide (s i≠t (permute v i))
    let make (v : Data) : Shuffle I := (permute v,orient v)
    have fits (v : Data) : fitsThree (make v) s t := by
      intro i
      have choice := same_kind (s i) (t (permute v i)) (classEq v i).symm
      change turnPair (orient v i) (s i)=t (permute v i)
      by_cases d : (s i).1=(s i).2
      · have swap : (s i).swap=s i := Prod.ext d.symm d
        have h := choice.elim id (fun e => swap ▸ e)
        cases orient v i <;> simpa [turnPair,swap] using h
      · by_cases same : s i=t (permute v i)
        · have bit : orient v i=false := by simp only [orient,dif_neg d,ne_eq,same,not_true_eq_false,decide_false]
          simpa [bit,turnPair] using same
        · simpa [orient,d,same,turnPair] using choice.resolve_left same
    let encode (v : Data) : {q : Shuffle I // fitsThree q s t} := ⟨make v,fits v⟩
    have inj : Function.Injective encode := by
      intro v w h
      have hp : permute v=permute w := congrArg (fun z => (z.val : Shuffle I).1) h
      have ho : orient v=orient w := congrArg (fun z => (z.val : Shuffle I).2) h
      apply Prod.ext
      · funext j
        ext i
        obtain ⟨i,rfl⟩ := i
        exact congrArg (fun p : Equiv.Perm I => p i) hp
      · funext i
        simpa [orient,i.property] using congrFun ho i.val
    have cardK (a : Colors3 I) (j : Fin 6) : Fintype.card (K a j)=sizeThree a j :=
      Fintype.card_subtype _
    have each (j : Fin 6) : Fintype.card (K s j ≃ K t j)=(sizeThree s j).factorial := by
      let e : K s j ≃ K t j := Fintype.equivOfCardEq (by rw [cardK,cardK,eq])
      rw [Fintype.card_equiv e,cardK]
    have er : Fintype.card R=diagonal s := Fintype.card_subtype _
    have le := Fintype.card_le_of_injective encode inj
    rw [show Fintype.card Data=Fintype.card (∀ j,K s j ≃ K t j)*Fintype.card (R→Bool)
      from Fintype.card_prod _ _,Fintype.card_pi,Fintype.card_fun,Fintype.card_bool,er,Fintype.card_subtype] at le
    simpa only [priceThree,if_pos eq,each] using le
  · simp [priceThree,eq]

end WildAnchor
