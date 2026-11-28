import RootContraction
import MatchingCuts

namespace WildExact.RootContraction
open Finset WildDeletion
variable {n : Nat}

/-- The side missing the former root partner is paired internally by its color.
Consequently every nonempty far side has odd size on an odd deletion. -/
theorem odd_far (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    (a c : Fin n) (hn : n%2=1) (ne : (far g w a c).Nonempty) : (far g w a c).card%2=1 := by
  classical
  let S := far g w a c
  let emb := Fin.castLEEmb (Nat.le_succ n)
  let T := Sᶜ.map emb
  have excluded : partner g c∈S := by
    obtain ⟨x,hx⟩ := ne
    have h := (two_components g win a c x).resolve_left (mem_far.mp hx)
    exact mem_far.mpr (fun p => mem_far.mp hx (p.join h))
  have closed : WildSieve.Closed (mate g c) T := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    have inside : x∉S := mem_compl.mp hx
    have reachable := not_not.mp (fun h => inside (mem_far.mpr h))
    have spec := mate_spec g c x.castSucc
    have notRoot : mate g c x.castSucc≠Fin.last n := by
      intro eq
      rw [eq,g.symm] at spec
      exact inside ((partner_unique g c x spec.2).symm ▸ excluded)
    obtain ⟨y,hy⟩ := WildSieve.before_root _ notRoot
    have edge : Joined (restrict g) (shrink a w) c x y := Or.inr ⟨
      fun e => spec.1 (by rw [←hy,e]),by change g.paint x.castSucc y.castSucc=c; rw [hy]; exact spec.2⟩
    exact mem_map.mpr ⟨y,mem_compl.mpr (fun bad => mem_far.mp bad (.step reachable edge)),hy⟩
  have count := WildSieve.closed_size (mate_involutive g c) (fun v => (mate_spec g c v).1) closed
  change (Sᶜ.map emb).card=_ at count
  rw [card_map,card_compl,Fintype.card_fin] at count
  have le := card_le_univ S
  simp only [Fintype.card_fin] at le
  change S.card%2=1
  omega
#print axioms odd_far
end WildExact.RootContraction
