import ActiveFrames30
import DuplicateMeans30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) frameIncEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable def present (F : Factor V C) (L : Finset V) (D : Deck) (t : Fin 3) :=
  (frames F L t).filter fun P => D∈frameEvent L P

theorem present_mem {F : Factor V C} {L : Finset V} {D : Deck} {t : Fin 3} {P : Pattern}
    (seen : D∈localSeal univ L) : P∈present F L D t ↔
      P∈family F ∧ (vertices P∩L).card=6-3*t.val ∧ P⊆D.val := by
  constructor
  · intro h
    obtain ⟨f,event⟩ := mem_filter.mp h
    exact ⟨(mem_filter.mp f).1,(mem_filter.mp f).2.1,(mem_filter.mp (mem_inter.mp event).2).2⟩
  · rintro ⟨p,k,sub⟩
    have both : D∈frameEvent L P := mem_inter.mpr ⟨seen,mem_filter.mpr ⟨mem_univ _,sub⟩⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨p,k,D,both⟩,both⟩

theorem present_image (F : Factor V C) (L : Finset V) (D : Deck) (t : Fin 3) (seen : D∈localSeal univ L) :
    (present F L D t).image vertices=sideHits F L D t := by
  ext Q
  constructor
  · intro h
    obtain ⟨P,p,rfl⟩ := mem_image.mp h
    obtain ⟨m,kind,sub⟩ := (present_mem seen).mp p
    obtain ⟨ok,hmark⟩ := SixCounts.pattern_mem.mp m
    exact mem_filter.mpr ⟨hmark,kind,local_seal_mem.mpr ⟨⟨P,ok,rfl⟩,sub⟩⟩
  · intro h
    obtain ⟨mark,kind,closed⟩ := mem_filter.mp h
    obtain ⟨P,sub⟩ := local_seal_mem.mp closed
    exact mem_image.mpr ⟨P.val,(present_mem seen).mpr ⟨SixCounts.pattern_mem.mpr ⟨P.property.1,
      P.property.2.symm ▸ mark⟩,P.property.2.symm ▸ kind,sub⟩,P.property.2⟩

private theorem determined (D : Deck) (P R : Pattern) (p : P⊆D.val) (r : R⊆D.val)
    (eq : vertices P=vertices R) : P=R := by
  have incl (A B : Pattern) (a : A⊆D.val) (b : B⊆D.val) (same : vertices A=vertices B) : A⊆B := by
    intro S hs
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<S.card by rw [D.property.1.size S (a hs)]; decide)
    obtain ⟨T,ht,vt⟩ := mem_biUnion.mp (show v∈vertices B from same ▸ block_sub hs hv)
    exact (D.property.1.only (a hs) (b ht) hv vt).symm ▸ ht
  exact Subset.antisymm (incl _ _ p r eq) (incl _ _ r p eq.symm)

theorem sum_present (F : Factor V C) (L : Finset V) (D : Deck) (t : Fin 3) (seen : D∈localSeal univ L)
    (w : Finset V → ℚ) : (∑ Q∈sideHits F L D t,w Q)=∑ P∈present F L D t,w (vertices P) := by
  rw [←present_image F L D t seen]
  apply sum_image
  intro P hp R hr eq
  exact determined D _ _ ((present_mem seen).mp hp).2.2 ((present_mem seen).mp hr).2.2 eq

noncomputable def frameAvg (F : Factor V C) (L : Finset V) (t : Fin 3) (w : Pattern → ℚ) :=
  (∑ P∈frames F L t,(frameEvent L P).card*w P)/sideWays

theorem sum_frames (F : Factor V C) (L : Finset V) (t : Fin 3) (w : Pattern → ℚ) :
    frameAvg F L t w = sideAvg L (fun D => ∑ P∈present F L D t,w P) := by
  classical
  unfold frameAvg sideAvg localSum present
  simp_rw [sum_filter]
  rw [sum_comm (s:=localSeal univ L)]
  congr 1
  apply sum_congr rfl
  intro P _
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  have eq : (localSeal univ L).filter (fun D => D∈frameEvent L P)=frameEvent L P := by
    ext D; simp [frameEvent]
  rw [eq]

private theorem sum_hit_weight (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (w : Finset V → ℚ) :
    sideAvg L (fun D => ∑ Q∈sideHits F L D t,w Q)=∑ Q∈marks F univ,markWeight L Q t*w Q := by
  classical
  apply (div_eq_iff (by decide : (sideWays : ℚ)≠0)).mpr
  unfold localSum sideHits
  simp_rw [sum_filter]
  rw [sum_comm,sum_mul]
  apply sum_congr rfl
  intro Q h
  have count := split_mark_weight L Q l (mark_mem.mp h).2.1 t
  by_cases ty : (Q∩L).card=6-3*t.val
  · simp only [ty,true_and,ite_true,←sum_filter,sum_const,nsmul_eq_mul,filter_mem_eq_inter] at count ⊢
    rw [count]
    ring
  · simp [ty,markWeight]

theorem frame_mark_average (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (w : Finset V → ℚ) :
    frameAvg F L t (fun P => w (vertices P))=∑ Q∈marks F univ,markWeight L Q t*w Q := by
  rw [sum_frames,←sum_hit_weight F L l t w]
  unfold sideAvg localSum
  congr 1
  exact sum_congr rfl (fun D hd => (sum_present F L D t hd w).symm)

theorem frame_mass (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) :
    frameAvg F L t (fun _ => 1)=conditionalMean F L t := by
  simpa [conditionalMean] using frame_mark_average F L l t (fun _ => 1)

theorem frame_closing (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (c : C) :
    frameAvg F L t (fun P => if c∈owners F (vertices P) then 1 else 0)=first t (Inside F c L) := by
  rw [frame_mark_average F L l t (fun Q => if c∈owners F Q then 1 else 0)]
  simp only [mul_ite,mul_one,mul_zero,←sum_filter]
  have eq : (marks F univ).filter (fun Q => c∈owners F Q)=candidates F c ∅ univ 6 := by
    ext Q
    simp only [mem_filter,mark_mem,owner_mem,candidate_mem,empty_union,subset_univ,true_and]
    tauto
  rw [eq,color_first F c L l t]

end WildSieve.Thirty.Graph
