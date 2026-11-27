import GlobalCount
namespace WildExact.Seventeen

private def findBig (p : V → Bool) := bigIndex[encode p]?.getD 0

private def findSmall (rel : Slot → Slot → Bool) := Id.run do
  let slotOf := fun x : Fin 12 => Fin.ofNat' 14 x.val
  let triples := (List.finRange 12).map fun x => encode (fun y : Fin 12 => rel (slotOf x) (slotOf y))
  return partIndexMap.getD (partKey triples.eraseDups) 0

private theorem bigRead : ∀ b : Big,findBig (fun x => slot b x==12)=b.val := by native_decide
private theorem smallRead : ∀ p : Small,findSmall (fun u v => tag p u==tag p v)=p.val := by native_decide

private theorem five (l : Layout) (x : V) :
    (((List.finRange 18).filter (sameBlock l x)).length==5) = (slot l.1 x==12) := by
  have perm := ((layout_shape l).filter (fun a => owner l x == a)).length_eq
  simp only [List.filter_map,List.length_map,Function.comp_def] at perm
  change ((List.filter (fun y => owner l x==owner l y) _).length==5) = _
  rw [perm]
  have sizes : ∀ b : Block, ((K17Connectivity.labels.filter (fun a => b==a)).length==5)=(b==1) := by decide
  have tags : ∀ (p : Small) (u : Slot),(tag p u==1)=(u==12) := by native_decide
  exact (sizes _).trans (tags _ _)

/-- Distinct layout indices give distinct partitions even when block names are ignored. -/
theorem distinct_layouts (l m : Layout) (same : ∀ x y,sameBlock l x y=sameBlock m x y) : l=m := by
  obtain ⟨b,p⟩ := l
  obtain ⟨d,t⟩ := m
  have bits : (fun x => slot b x==12)=(fun x => slot d x==12) := by
    funext x
    rw [←five (b,p) x,←five (d,t) x,funext (same x)]
  have bd : b=d := Fin.ext ((bigRead b).symm.trans ((congrArg findBig bits).trans (bigRead d)))
  subst d
  have cover : ∀ (b : Big) (u : Slot), ∃ x : V,slot b x=u := by native_decide
  have pattern : (fun u v => tag p u==tag p v)=(fun u v => tag t u==tag t v) := by
    funext u v
    obtain ⟨x,rfl⟩ := cover b u
    obtain ⟨y,rfl⟩ := cover b v
    exact same x y
  have pt : p=t := Fin.ext ((smallRead p).symm.trans ((congrArg findSmall pattern).trans (smallRead t)))
  rw [pt]

/-- Count groupings as equivalence relations on points, independently of the
order in which their blocks or their indices were stored. -/
theorem distinct_successes (g : Coloring 17 17) :
    403637 ≤ (((Finset.univ : Finset Layout).filter
      (fun l => (failing (partners g) l).card=0)).image sameBlock).card := by
  classical
  have inj : Function.Injective sameBlock := fun {l m} eq =>
    distinct_layouts l m (fun x y => congrFun (congrFun eq x) y)
  rw [Finset.card_image_of_injective _ inj]
  have h := many_wins g
  unfold wins at h
  rw [←Finset.sum_filter] at h
  simp only [Finset.sum_const, nsmul_one] at h
  exact_mod_cast h

#print axioms distinct_successes
end WildExact.Seventeen
