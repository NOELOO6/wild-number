import OrderedMotifs30

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion
variable {τ : Type} [DecidableEq τ]

def pairPool (S : Finset τ) := (S ×ˢ S).filter (fun p => p.2≠p.1)
def triplePool (S : Finset τ) := (S ×ˢ (S ×ˢ S)).filter (fun p =>
  p.2.1≠p.1 ∧ p.2.2≠p.1 ∧ p.2.2≠p.2.1)
def pairKey (p : τ × τ) : Finset τ := {p.1,p.2}
def tripleKey (p : τ × τ × τ) : Finset τ := {p.1,p.2.1,p.2.2}

theorem sum_pool (S : Finset τ) (f : τ → τ → τ → Nat) :
    (∑ v∈triplePool S,f v.1 v.2.1 v.2.2)=orderedThree S f := by
  classical
  simp only [triplePool,sum_filter,sum_product,orderedThree,←filter_ne',sum_filter]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  by_cases pq : q=p
  · simp [pq]
  · rw [if_pos pq]
    apply sum_congr rfl
    intro r _
    by_cases rp : r=p <;> by_cases rq : r=q <;> simp [pq,rp,rq]

private theorem group_keys {σ : Type} [DecidableEq σ] (S : Finset τ) (k : Nat)
    (pool : Finset σ) (key : σ → Finset τ) (w : σ → Nat)
    (h : ∀ v∈pool,key v∈S.powersetCard k) :
    (∑ J∈S.powersetCard k,∑ v∈pool.filter (fun v => key v=J),w v)=∑ v∈pool,w v := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simp [h _ hv]

private theorem triple_fiber (S J : Finset τ) (sub : J⊆S) (num : J.card=3) :
    (triplePool S).filter (fun v => tripleKey v=J)=triplePool J := by
  ext v
  rcases v with ⟨p,q,r⟩
  simp only [triplePool,mem_filter,mem_product,tripleKey]
  constructor
  · rintro ⟨⟨_,sep⟩,rfl⟩
    exact ⟨⟨by simp,by simp,by simp⟩,sep⟩
  · rintro ⟨⟨pj,qj,rj⟩,sep⟩
    have ds := sep
    obtain ⟨qp,rp,rq⟩ := ds
    have set : ({p,q,r} : Finset τ).card=3 := by simp [Ne.symm qp,Ne.symm rp,Ne.symm rq]
    exact ⟨⟨⟨sub pj,sub qj,sub rj⟩,sep⟩,eq_of_subset_of_card_le
      (insert_subset pj (insert_subset qj (singleton_subset_iff.mpr rj))) (by omega)⟩

theorem sum_triples (S : Finset τ) (f : τ → τ → τ → Nat) :
    (∑ J∈S.powersetCard 3,orderedThree J f)=orderedThree S f := by
  have member (v : τ × τ × τ) (hv : v∈triplePool S) : tripleKey v∈S.powersetCard 3 := by
    rcases v with ⟨p,q,r⟩
    obtain ⟨hs,qp,rp,rq⟩ := mem_filter.mp hv
    obtain ⟨pS,qrS⟩ := mem_product.mp hs
    obtain ⟨qS,rS⟩ := mem_product.mp qrS
    exact mem_powersetCard.mpr ⟨insert_subset pS (insert_subset qS (singleton_subset_iff.mpr rS)),
      by simp [tripleKey,Ne.symm qp,Ne.symm rp,Ne.symm rq]⟩
  have h := group_keys S 3 (triplePool S) tripleKey (fun v => f v.1 v.2.1 v.2.2) member
  rw [←sum_pool]
  rw [←h]
  apply sum_congr rfl
  intro J hJ
  rw [triple_fiber S J (mem_powersetCard.mp hJ).1 (mem_powersetCard.mp hJ).2,sum_pool]

theorem sum_pairs (S : Finset τ) (w : Finset τ → Nat) :
    (∑ v∈pairPool S,w (pairKey v))=2*bill w 2 S := by
  have member (v : τ×τ) (hv : v∈pairPool S) : pairKey v∈S.powersetCard 2 := by
    obtain ⟨hs,ne⟩ := mem_filter.mp hv
    exact mem_powersetCard.mpr ⟨insert_subset (mem_product.mp hs).1
      (singleton_subset_iff.mpr (mem_product.mp hs).2),by simp [pairKey,Ne.symm ne]⟩
  rw [←group_keys S 2 (pairPool S) pairKey (fun v => w (pairKey v)) member,bill,mul_sum]
  apply sum_congr rfl
  intro J hJ
  obtain ⟨sub,num⟩ := mem_powersetCard.mp hJ
  obtain ⟨p,q,pq,rfl⟩ := card_eq_two.mp num
  have hp := sub (mem_insert_self _ _)
  have hq := sub (mem_insert_of_mem (mem_singleton_self _))
  have eq : (pairPool S).filter (fun v => pairKey v={p,q})= {(p,q),(q,p)} := by
    ext v
    rcases v with ⟨x,y⟩
    simp only [pairPool,mem_filter,mem_product,pairKey,mem_insert,mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_,yx⟩,keys⟩
      have a : x∈({p,q} : Finset τ) := keys ▸ mem_insert_self _ _
      have b : y∈({p,q} : Finset τ) := keys ▸ mem_insert_of_mem (mem_singleton_self _)
      simp only [mem_insert,mem_singleton] at a b
      rcases a with rfl|rfl <;> rcases b with rfl|rfl <;> simp_all
    · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · exact ⟨⟨⟨hp,hq⟩,pq.symm⟩,rfl⟩
      · exact ⟨⟨⟨hq,hp⟩,pq⟩,pair_comm _ _⟩
  rw [eq]
  have ne : (p,q)≠(q,p) := fun e => pq (Prod.mk.inj e).1
  simp [ne,pairKey,pair_comm q p,two_mul]

end WildSieve.Thirty.Motifs
