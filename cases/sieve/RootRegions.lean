import PairRegions
namespace WildSieve
open Finset
variable {I V : Type} [DecidableEq I] [DecidableEq V] [Fintype V]

noncomputable def rootHits (X : Finset V) (P : Finset I) (edge : I → Finset V) (z : V) :=
  P.biUnion (fun i => localSeal X (insert z (edge i)))

omit [DecidableEq I] in
theorem root_coverage (X : Finset V) (P : Finset I) (edge : I → Finset V) (z : V)
    (sz : ∀ i∈P,(edge i).card=2) (apart : (P : Set I).PairwiseDisjoint edge)
    (inside : points edge P⊆X) (zx : z∈X) (free : z∉points edge P)
    (j : Nat) (len : X.card=3*j) (lo : 1≤j) : (rootHits X P edge z).card=P.card*ways (j-1) := by
  classical
  let E (i) := localSeal X (insert z (edge i))
  have one (i) (hi : i∈P) : edge i⊆points edge P := fun _ hv => mem_biUnion.mpr ⟨i,hi,hv⟩
  have dis : (P : Set I).PairwiseDisjoint E := by
    intro a ha b hb ab
    apply disjoint_left.mpr
    intro D da db
    have dv := intersect_sealed da db
    have eq : insert z (edge a) ∩ insert z (edge b)={z} := by
      ext x
      simp only [mem_insert,mem_inter,mem_singleton]
      exact ⟨fun ⟨u,v⟩ => u.elim id (fun e => v.elim id (fun f => (disjoint_left.mp (apart ha hb ab) e f).elim)),
        fun h => ⟨Or.inl h,Or.inl h⟩⟩
    rw [eq,card_singleton] at dv
    omega
  have each (i) (hi : i∈P) : (E i).card=ways (j-1) := by
    have n : z∉edge i := fun h => free (one i hi h)
    have size : (insert z (edge i)).card=3 := by simp [n,sz i hi]
    simpa only [show ways 1=1 by decide,one_mul] using local_seal_card X _ 1 (j-1)
      (insert_subset zx ((one i hi).trans inside)) size (by omega)
  rw [rootHits,card_biUnion dis,sum_congr rfl each,sum_const]
  simp [nsmul_eq_mul]

theorem cross_coverage (X : Finset V) (P : Finset I) (edge : I → Finset V) (z : V)
    (sz : ∀ i∈P,(edge i).card=2) (apart : (P : Set I).PairwiseDisjoint edge)
    (inside : points edge P⊆X) (zx : z∈X) (free : z∉points edge P)
    (j : Nat) (len : X.card=3*j) (lo : 3≤j) :
    (sixHits X P edge∩rootHits X P edge z).card ≤
      P.card.choose 3*((P.card-3)*(10*ways (j-3))) := by
  classical
  let H := P.powersetCard 3
  let A (s : Finset I) := localSeal X (points edge s)
  let B (i : I) := localSeal X (insert z (edge i))
  have inc (i) (hi : i∈P) : edge i⊆points edge P := fun _ hv => mem_biUnion.mpr ⟨i,hi,hv⟩
  have one (s) (hs : s∈H) (i) (hi : i∈P) : (A s∩B i).card ≤ if i∈s then 0 else 10*ways (j-3) := by
    obtain ⟨sp,sc⟩ := mem_powersetCard.mp hs
    have ssub := points_mono edge sp
    by_cases mem : i∈s
    · rw [if_pos mem]
      apply Nat.le_zero.mpr (card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_))
      intro D h
      have div := intersect_sealed (mem_inter.mp h).1 (mem_inter.mp h).2
      have eq : points edge s∩insert z (edge i)=edge i := by
        ext v
        constructor
        · rintro h
          obtain ⟨inS,hm⟩ := mem_inter.mp h
          exact (mem_insert.mp hm).resolve_left fun eq => free (eq ▸ ssub inS)
        · exact fun h => mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,mem,h⟩,mem_insert_of_mem h⟩
      rw [eq,sz i hi] at div
      omega
    · rw [if_neg mem]
      have dis : Disjoint (points edge s) (insert z (edge i)) := by
        apply disjoint_left.mpr
        intro v vs vb
        rcases mem_insert.mp vb with eq|e
        · exact free (eq ▸ ssub vs)
        obtain ⟨a,ha,va⟩ := mem_biUnion.mp vs
        exact disjoint_left.mp (apart (sp ha) hi (fun eq => mem (eq ▸ ha))) va e
      have six := points_size P edge sz apart sp
      rw [sc] at six
      have nz : z∉edge i := fun hv => free (inc i hi hv)
      have three : (insert z (edge i)).card=3 := by simp [nz,sz i hi]
      simpa only [show ways 2*ways 1=10 by decide] using joint_local_bound X _ _ 2 1 (j-3)
        (ssub.trans inside) (insert_subset zx ((inc i hi).trans inside)) dis (by omega) three (by omega)
  have cover : sixHits X P edge∩rootHits X P edge z ⊆ H.biUnion (fun s => P.biUnion (fun i => A s∩B i)) := by
    intro D hd
    obtain ⟨s,hs,da⟩ := mem_biUnion.mp (mem_inter.mp hd).1
    obtain ⟨i,hi,db⟩ := mem_biUnion.mp (mem_inter.mp hd).2
    exact mem_biUnion.mpr ⟨s,hs,mem_biUnion.mpr ⟨i,hi,mem_inter.mpr ⟨da,db⟩⟩⟩
  have row (s) (hs : s∈H) : (P.biUnion (fun i => A s∩B i)).card ≤ (P.card-3)*(10*ways (j-3)) := by
    apply card_biUnion_le.trans ((sum_le_sum (fun i hi => one s hs i hi)).trans ?_)
    have eq : (∑ i∈P,if i∈s then 0 else 10*ways (j-3))=∑ _∈P \ s,10*ways (j-3) := by
      rw [sdiff_eq_filter]
      simp only [sum_filter,ite_not]
    rw [eq,sum_const,card_sdiff (mem_powersetCard.mp hs).1,(mem_powersetCard.mp hs).2]
    simp [nsmul_eq_mul]
  apply (card_le_card cover).trans (card_biUnion_le.trans ((sum_le_sum row).trans ?_))
  simp [H,nsmul_eq_mul]
end WildSieve
