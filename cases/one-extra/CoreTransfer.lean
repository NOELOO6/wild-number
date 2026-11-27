import TwoCore19
import TwoCore21
import TwoCore23
import Core21Trap
import MatchingModel
namespace WildCuts.OneExtra
open Finset WildExact WildDeletion

/-- When all wild edges avoid the last vertex, adding that vertex preserves
success and failure for the same edge set. In each color it is a leaf. -/
theorem same_lines {n : Nat} (hn : 0<n) (g : Coloring (n+1) n) (w : Lines n) :
    Works g (w.map liftLine) ↔ Works (restrict g) w := by
  constructor
  · intro good c x y
    let f (v : Fin n) := g.paint (Fin.last n) v.castSucc
    have inj : Function.Injective f := fun a b h => Fin.castSucc_injective n
      (g.proper _ _ _ (Fin.ne_of_gt (Fin.castSucc_lt_last _)) (Fin.ne_of_gt (Fin.castSucc_lt_last _)) h)
    obtain ⟨p,hp⟩ := (Finite.injective_iff_surjective.mp inj) c
    let q : Fin (n+1) → Fin n := Fin.lastCases p id
    have old (a : Fin n) : q a.castSucc=a := Fin.lastCases_castSucc _
    have last : q (Fin.last n)=p := Fin.lastCases_last
    have project {a b} (edge : Joined g (w.map liftLine) c a b) : Walk (Joined (restrict g) w c) (q a) (q b) := by
      have wild {u v : Fin (n+1)} (e : (u,v)∈w.map liftLine) : Touch w (q u) (q v) := by
        obtain ⟨⟨s,t⟩,mem,eq⟩ := mem_map.mp e
        cases eq
        change Touch w (q s.castSucc) (q t.castSucc)
        rw [old,old]
        exact Or.inl mem
      rcases edge with (e|e)|⟨ne,col⟩
      · exact .step (.stay _) (Or.inl (wild e))
      · exact .step (.stay _) (Or.inl (wild e).symm)
      cases a using Fin.lastCases with
      | last =>
        cases b using Fin.lastCases with
        | last => exact .stay _
        | cast b =>
          have eq : b=p := inj (col.trans hp.symm)
          rw [last,old,eq];exact .stay _
      | cast a =>
        cases b using Fin.lastCases with
        | last =>
          have eq : a=p := inj ((g.symm (Fin.last n) a.castSucc).trans (col.trans hp.symm))
          rw [last,old,eq];exact .stay _
        | cast b =>
          rw [old,old]
          exact .step (.stay _) (Or.inr ⟨fun ab => ne (congrArg Fin.castSucc ab),col⟩)
    simpa only [old] using Walk.mapInto q (fun _ _ e => project e) (good c x.castSucc y.castSucc)
  · intro good
    let r : Fin n := ⟨0,hn⟩
    have meets : MeetsCore (restrict g) w {r} := fun c x => ⟨r,mem_singleton_self _,good c x r⟩
    have up := lift_meets g meets
    intro c a b
    obtain ⟨x,hx,left⟩ := up c a
    obtain ⟨y,hy,right⟩ := up c b
    have xr : x=r.castSucc := by simpa using hx
    have yr : y=r.castSucc := by simpa using hy
    have xy := xr.trans yr.symm
    exact left.join (xy ▸ backwards (joined_symm g) right)

theorem even_example {n b : Nat} (odd : n%2=1) (lo : 3≤n) (g : Coloring n n)
    (proof : Exact g b) (budget : b=(2*n+2)/3) : Exact (augment odd g) b := by
  subst b
  obtain ⟨⟨w,leg,sz,ok⟩,_⟩ := proof
  apply exact_of_upper (upper_from_deletion _ ?_)
  · exact fun _ => even_lower (by omega) _
  rw [restrict_augment]
  exact ⟨w,leg,sz.le,ok⟩

theorem examples_even :
    Exact (augment (by decide) Trap19.graph) 13 ∧ Exact (augment (by decide) Trap21.graph) 14 ∧
    Exact (augment (by decide) Trap23.graph) 16 :=
  ⟨even_example (by decide) (by decide) _ Trap19.repaired_exact rfl,
   even_example (by decide) (by decide) _ Trap21.repaired_exact rfl,
   even_example (by decide) (by decide) _ Trap23.repaired_exact rfl⟩

#print axioms same_lines
#print axioms examples_even
end WildCuts.OneExtra
