import BarrierRows
import MatchingModel
namespace WildRectangle
open Finset WildExact
variable {V C : Type} [DecidableEq V] [DecidableEq C] [Fintype V]

def Eligible (L : Rows V C) (r a b d : V) :=
  L.row r d≠L.row a b ∧ L.row b d≠L.row r a ∧ L.row a d≠L.row r b

/-- With a common blank diagonal and symmetric labels, every prescribed
pair extends to two ordinary triples whose nine crossing edges are rainbow. -/
theorem latin_rectangle (L : Rows V C) (blank : C)
    (diag : ∀ v,L.row v v=blank) (sym : ∀ v w,L.row v w=L.row w v)
    (size : Fintype.card V=16) (r a b : V) (ra : r≠a) (rb : r≠b) (ab : a≠b) :
    ∃ d,d∉({r,a,b}:Finset V) ∧ Eligible L r a b d ∧
      Rectangle L {a,b,d} ({r,a,b,d}:Finset V)ᶜ := by
  classical
  let p := transition L a b
  let base : Finset V := {r,a,b}
  let V0 := baseᶜ
  have baseSize : base.card=3 := by simp [base,ra,rb,ab]
  have v0size : V0.card=13 := by simp [V0,card_compl,size,baseSize]
  have p_a : p a=b := (L.row b).symm_apply_eq.mpr ((diag a).trans (diag b).symm)
  have p_b : p b=a := (L.row b).symm_apply_eq.mpr (sym a b)
  have prr : p r≠r := by
    intro eq
    exact ab (L.column r ((L.row b).symm_apply_eq.mp eq))
  have pra : p r≠a := fun h => rb (p.injective (h.trans p_b.symm))
  have prb : p r≠b := fun h => ra (p.injective (h.trans p_a.symm))
  have pr_in : p r∈V0 := by simp [V0,base,prr,pra,prb]
  let U := V0.erase (p r)
  have cap : U.card≤12 := by rw [show U=V0.erase (p r) from rfl,card_erase_of_mem pr_in,v0size]
  let exc : Finset V := {(L.row r).symm (L.row a b),(L.row b).symm (L.row r a),(L.row a).symm (L.row r b)}
  let E := V0 \ exc
  have room : 10≤E.card := by
    have bound := card_sdiff_add_card_inter V0 exc
    have interSize : (V0∩exc).card≤3 := (card_le_card inter_subset_right).trans (Finset.card_le_three)
    change 10≤(V0 \ exc).card
    omega
  have outside (d) (h : d∈E) : d∉base := mem_compl.mp (mem_sdiff.mp h).1
  have clean (d) (h : d∈E) : Eligible L r a b d := by
    have misses := (mem_sdiff.mp h).2
    dsimp [exc] at misses
    simp only [mem_insert,mem_singleton,not_or] at misses
    exact ⟨fun q => misses.1 ((L.row r).symm_apply_eq.mpr q.symm).symm,
      fun q => misses.2.1 ((L.row b).symm_apply_eq.mpr q.symm).symm,
      fun q => misses.2.2 ((L.row a).symm_apply_eq.mpr q.symm).symm⟩
  by_contra! none
  let Q := U.powerset.filter (fun X => Seven p U X ∧ a∈rowSet L a X ∧ b∈rowSet L a X)
  have good (X) (hx : X∈Q) := (mem_filter.mp hx).2
  have rowBound := barrier_union L a b ab U cap Q good
  let covered := Q.biUnion (rowSet L a)
  have trapped (d) (de : d∈E) : d∈covered ∧ a∈covered ∧ b∈covered := by
    have no := outside d de
    simp only [base,mem_insert,mem_singleton,not_or] at no
    obtain ⟨dr,da,db⟩ : d≠r ∧ d≠a ∧ d≠b := no
    let A : Finset V := {a,b,d}
    let S : Finset V := ({r,a,b,d}:Finset V)ᶜ
    have sz : A.card=3 := by simp [A,ab,da.symm,db.symm]
    have sc : S.card=12 := by simp [S,card_compl,size,ra,rb,dr.symm,ab,da.symm,db.symm]
    have sub : S⊆V0 := by
      intro v h
      apply mem_compl.mpr
      intro hb
      exact mem_compl.mp h (by rcases (show v=r ∨ v=a ∨ v=b by simpa [base] using hb) with e|e|e <;> simp [e])
    let k := L.row a b
    let x := (L.row d).symm k
    have hit : L.row d x=k := (L.row d).apply_symm_apply k
    have xr : x≠r := fun h => (clean d de).1 ((sym r d).trans ((congrArg (L.row d) h).symm.trans hit))
    have xa : x≠a := by
      intro h
      have ad : L.row a d=L.row a b := (sym a d).trans ((congrArg (L.row d) h).symm.trans hit)
      exact db ((L.row a).injective ad)
    have xb : x≠b := fun h => da (L.column b ((congrArg (L.row d) h).symm.trans hit))
    have xd : x≠d := by
      intro h
      have eq : L.row a b=L.row a a := hit.symm.trans ((congrArg (L.row d) h).trans ((diag d).trans (diag a).symm))
      exact ab ((L.row a).injective eq).symm
    have xp : x∈S := by simp [S,xr,xa,xb,xd]
    have aa : a∈A := by simp [A]
    have bb : b∈A := by simp [A]
    have dd : d∈A := by simp [A]
    have only (y : V) (ys : y∈S) (ky : k∈palette L A y) : y=x := by
      obtain ⟨i,ia,eq⟩ := mem_image.mp ky
      simp only [A,mem_insert,mem_singleton] at ia
      rcases ia with ei|ei|ei <;> subst i
      · have e : y=b := (L.row a).injective eq
        exact False.elim (mem_compl.mp ys (by simp [e]))
      · have e : y=a := (L.row b).injective (eq.trans (sym a b))
        exact False.elim (mem_compl.mp ys (by simp [e]))
      · exact (L.row d).injective (eq.trans hit.symm)
    have alt := rectangle_or_seven L a b d ab A S V0 aa bb dd sz sc.ge sub
      ⟨x,xp,k,mem_image.mpr ⟨d,dd,hit⟩,only⟩
    have noWin : ¬Rectangle L A S := none d (outside d de) (clean d de)
    obtain ⟨Y,sv,ay,by_,dy⟩ := alt.resolve_left noWin
    have notR : r∉Y := fun h => mem_compl.mp (sv.sub h) (by simp [base])
    have yu : Y⊆U := fun v hv => mem_erase.mpr ⟨fun eq => notR ((sv.stable r).mp (eq ▸ hv)),sv.sub hv⟩
    have yq : Y∈Q := mem_filter.mpr ⟨mem_powerset.mpr yu,⟨yu,sv.card,sv.stable,sv.long⟩,ay,by_⟩
    exact ⟨mem_biUnion.mpr ⟨Y,yq,dy⟩,mem_biUnion.mpr ⟨Y,yq,ay⟩,mem_biUnion.mpr ⟨Y,yq,by_⟩⟩
  obtain ⟨d,de⟩ := card_pos.mp (by omega : 0<E.card)
  obtain ⟨_,ac,bc⟩ := trapped d de
  have sub : insert a (insert b E)⊆covered := insert_subset ac (insert_subset bc (fun v hv => (trapped v hv).1))
  have nb : b∉E := fun h => outside _ h (by simp [base])
  have na : a∉E := fun h => outside _ h (by simp [base])
  have count := card_le_card sub
  rw [card_insert_of_not_mem (by simp [ab,na]),card_insert_of_not_mem nb] at count
  change covered.card≤11 at rowBound
  omega
end WildRectangle
