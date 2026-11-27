import ExactModel
namespace WildSieve
open Finset WildExact WildDeletion
variable {n : Nat}

def spokes (T : Finset (Fin n)) : Lines n :=
  if h : T.Nonempty then (T.erase (T.min' h)).image (fun x => (T.min' h,x)) else ∅

theorem spokes_legal (T : Finset (Fin n)) : Legal (spokes T) := by
  intro e he
  unfold spokes at he
  split at he
  next h =>
    obtain ⟨x,hx,rfl⟩ := mem_image.mp he
    exact lt_of_le_of_ne (min'_le _ _ (mem_erase.mp hx).2) (mem_erase.mp hx).1.symm
  next => simp at he

theorem spokes_bound (T : Finset (Fin n)) : (spokes T).card ≤ T.card-1 := by
  unfold spokes
  split
  next h =>
    exact card_image_le.trans (card_erase_of_mem (min'_mem _ h)).le
  next => simp

theorem in_star {T : Finset (Fin n)} {w : Lines n} (sub : spokes T⊆w)
    {x y : Fin n} (hx : x∈T) (hy : y∈T) : Walk (Touch w) x y := by
  let ne : T.Nonempty := ⟨x,hx⟩
  let r := T.min' ne
  have one (v : Fin n) (hv : v∈T) : Walk (Touch w) r v := by
    by_cases eq : v=r
    · exact eq ▸ Walk.stay _
    · apply Walk.step (E := Touch w) (.stay r) (Or.inl (sub ?_))
      rw [spokes,dif_pos ne]
      exact mem_image.mpr ⟨v,mem_erase.mpr ⟨eq,hv⟩,rfl⟩
  exact (backwards (fun h => Or.symm h) (one x hx)).join (one y hy)

def oldPart (T : Finset (Fin (n+1))) := univ.filter (fun x : Fin n => x.castSucc∈T)

theorem old_mem {T : Finset (Fin (n+1))} {x : Fin n} : x∈oldPart T ↔ x.castSucc∈T := by simp [oldPart]

theorem before_root (v : Fin (n+1)) (ne : v≠Fin.last n) : ∃ x : Fin n,x.castSucc=v := by
  cases v using Fin.lastCases with
  | last => exact (ne rfl).elim
  | cast x => exact ⟨x,rfl⟩

theorem old_size (T : Finset (Fin (n+1))) (nr : Fin.last n ∉ T) : (oldPart T).card=T.card := by
  apply card_bij (fun x _ => x.castSucc)
  · exact fun _ hx => old_mem.mp hx
  · exact fun _ _ _ _ eq => Fin.castSucc_injective _ eq
  · intro v hv
    obtain ⟨x,rfl⟩ := before_root v (fun eq => nr (eq ▸ hv))
    exact ⟨x,old_mem.mpr hv,rfl⟩

end WildSieve
