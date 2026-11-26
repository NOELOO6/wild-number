import SevenProfileCheck
import SevenBalanceCheck

namespace SevenProfile
open VertexRedraw ThreeStars EdgeWalk WildDeletion
open Teams (total total_cons)
set_option maxRecDepth 5000

def choose (f : V → V) : Nat → List V → R → R
  | _, [], acc => acc
  | 0, _::_, acc => acc
  | d+1, x::xs, acc =>
    choose f d (xs.filter fun z => z != x && z != f x) ((x,f x)::acc)

private theorem follows (p : R → Bool) (f : V → V) (inv : ∀ x, f (f x)=x)
    (ne : ∀ x, f x ≠ x) (d : Nat) (xs : List V) (acc : R)
    (len : xs.length ≤ d) (closed : ∀ x ∈ xs, f x ∈ xs)
    (checked : visit p d xs acc=true) : p (choose f d xs acc)=true := by
  induction d generalizing xs acc with
  | zero =>
    have : xs=[] := by simpa using len
    subst xs
    exact checked
  | succ d ih =>
    cases xs with
    | nil => exact checked
    | cons x xs =>
      have hy : f x ∈ xs := (List.mem_cons.mp (closed x (by simp))).resolve_left (ne x)
      apply ih
      · exact Nat.le_trans (List.length_filter_le ..) (Nat.le_of_succ_le_succ len)
      · intro z hz
        obtain ⟨mem,neq⟩ := List.mem_filter.mp hz
        have both : z≠x ∧ z≠f x := by simpa using neq
        have ax : f z ≠ x := fun h => both.2 (by simpa [inv] using congrArg f h)
        have ay : f z ≠ f x := fun h => both.1 (by simpa [inv] using congrArg f h)
        exact List.mem_filter.mpr ⟨(List.mem_cons.mp (closed z (by simp [mem]))).resolve_left ax,
          by simp [ax,ay]⟩
      · exact List.all_eq_true.mp checked _ hy

def matching (f : V → V) := choose f 16 points []
theorem certified (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x) :
    cert (matching f)=true := follows cert f inv ne 16 points [] (by decide)
      (fun _ _ => (by decide : ∀ x : V, x∈points) _) all_matching_profiles

private theorem chosenRespects (f : V → V) (d : Nat) (xs : List V) (acc : R)
    (h : respects f acc) : respects f (choose f d xs acc) := by
  induction d generalizing xs acc with
  | zero => cases xs <;> exact h
  | succ d ih =>
    cases xs with
    | nil => exact h
    | cons x xs => exact ih _ _ (fun e he =>
        (List.mem_cons.mp he).elim (fun eq => eq ▸ rfl) (h e))

private theorem bit_in_fold (s : Nat) (i : Fin 280) (ls : List Nat) (n : Nat)
    (mem : s ∈ ls) (set : (table[s]?.getD 0).testBit i.val=true) :
    (ls.foldl (fun v a => v ||| (table[a]?.getD 0)) n).testBit i.val=true := by
  have carry (zs : List Nat) (v) (hv : v.testBit i.val=true) :
      (zs.foldl (fun k a => k ||| (table[a]?.getD 0)) v).testBit i.val=true := by
    induction zs generalizing v with
    | nil => exact hv
    | cons a zs ih => exact ih _ (by simp [Nat.testBit_or,hv])
  induction ls generalizing n with
  | nil => simp at mem
  | cons a ls ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · exact carry ls _ (by rw [Nat.testBit_or,set,Bool.or_true])
    · exact ih _ tail

theorem connects (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x)
    (i : Fin 280) (ok : (shadow (matching f)).testBit i.val=false) :
    Connected (Adj (wild (atLayout i) ++ actualEdges f)) := by
  have checked := (Bool.and_eq_true_iff.mp (certified f inv ne)).1
  apply path_of_unblocked _ (all_geometry i) _ (by simpa using checked) _ inv ne
    (chosenRespects f 16 points [] (by simp [respects]))
  cases h : spoils (atLayout i) (matching f) with
  | false => exact h
  | true =>
    obtain ⟨s,mem,hit⟩ := List.any_eq_true.mp h
    have set := List.all_eq_true.mp (table_contains i) s (by simpa using hit)
    have bad := bit_in_fold s i _ 0 mem set
    rw [show (subsets (matching f)).foldl (fun v a => v ||| (table[a]?.getD 0)) 0 =
      shadow (matching f) from rfl,ok] at bad
    contradiction

def rcount (m : R) := count 32831 m-count 63 m
def wcount (m : R) := count 7 m+count 56 m
def xcount (m : R) := count 63 m-wcount m

private theorem cap_price (r w x : Nat) (hr : r ≤ 1) (hs : r+w+x ≤ 2) :
    cap r w x + 18*r + 6*(x%2) ≤ 28+30*w+6*x := by
  have bounds : ∀ (a : Fin 2) (b d : Fin 3), a.val+b.val+d.val ≤ 2 →
    cap a.val b.val d.val + 18*a.val + 6*(d.val%2) ≤ 28+30*b.val+6*d.val := by decide
  exact bounds ⟨r,by omega⟩ ⟨w,by omega⟩ ⟨x,by omega⟩ hs

private theorem lam_price (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x)
    (m : R) (eq : m = matching f) (sparse : count 32831 m ≤ 2)
    (openA : count 32775 m ≠ 2) (openB : count 32824 m ≠ 2)
    (mono : wcount m ≤ count 63 m ∧ count 63 m ≤ count 32831 m)
    (root : rcount m ≤ 1) :
    badCount (shadow m) + 18*rcount m + 6*(xcount m%2) ≤ 28+30*wcount m+6*xcount m := by
  have hc := (Bool.and_eq_true_iff.mp (certified f inv ne)).2
  rw [←eq] at hc
  have bound : badCount (shadow m) ≤ cap (rcount m) (wcount m) (xcount m) := by
    simpa [rcount,wcount,xcount,show ¬count 32831 m > 2 by omega,openA,openB] using hc
  have sz : rcount m+wcount m+xcount m≤2 := by
    simp only [rcount,xcount] at *
    omega
  have price := cap_price (rcount m) (wcount m) (xcount m) root sz
  omega

private theorem endpoint (m : R) (x : V) (h : (full m).testBit x.val=true) :
    ∃ e ∈ m, e.1=x ∨ e.2=x := by
  induction m with
  | nil => simp [full] at h
  | cons e es ih =>
    change ((full es) ||| mask e).testBit x.val=true at h
    rw [Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with tail|head
    · obtain ⟨q,mem,hit⟩ := ih tail
      exact ⟨q,List.mem_cons_of_mem _ mem,hit⟩
    · have side : ∀ a b z : V, (mask (a,b)).testBit z.val=true → a=z ∨ b=z := by decide
      exact ⟨e,List.mem_cons_self,side _ _ _ head⟩

private theorem hits_actual (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x)
    (e : Edge 16) : hits (matching f) e = decide (f e.1=e.2) := by
  have ok : respects f (matching f) := chosenRespects f 16 points [] (by simp [respects])
  have fullrow : full (matching f)=65535 := by
    simpa using (Bool.and_eq_true_iff.mp (certified f inv ne)).1
  apply Bool.eq_iff_iff.mpr
  simp only [hits,Bool.or_eq_true,List.contains_iff_mem,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · exact ok e h
    · exact (congrArg f (ok _ h)).symm.trans (inv e.2)
  · intro h
    obtain ⟨⟨a,b⟩,mem,hit⟩ := endpoint (matching f) e.1 (by
      rw [fullrow]; exact (by decide : ∀ x : V, (65535:Nat).testBit x.val=true) _)
    rcases e with ⟨u,v⟩
    rcases hit with hu|hu
    · change a=u at hu
      subst a
      have hb : b=v := (ok _ mem).symm.trans h
      subst b; exact Or.inl mem
    · change b=u at hu
      subst b
      have ha : a=v := ((congrArg f (ok _ mem)).symm.trans (inv a)).symm.trans h
      subst a; exact Or.inr mem

private theorem tally_total (es : R) (diff : ∀ e∈es,e.1≠e.2) (f : C → V → V)
    (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (cover : ∀ x y : V, x≠y → ∃ c, f c x=y) :
    total colors (fun c => tally (matching (f c)) es) = es.length := by
  unfold tally
  rw [Teams.transpose]
  have eq := Teams.constant_total es (fun e => total colors (fun c =>
    if hits (matching (f c)) e then 1 else 0)) 1 (by
    intro e he
    obtain ⟨d,hd⟩ := cover _ _ (diff e he)
    have ind (c : C) : (if hits (matching (f c)) e then 1 else 0) =
        (if c=d then 1 else 0) := by
      rw [hits_actual _ (inv c) (ne c)]; by_cases h : c=d
      · subst c; simp [hd]
      · have h' : f c e.1≠e.2 := fun eq => proper c d h _ (eq.trans hd.symm)
        simp [h,h']
    simp only [ind]
    exact (by decide : ∀ d : C, total colors (fun c => if c=d then 1 else 0)=1) d)
  simpa using eq

private theorem sum_price {α} (xs : List α) (l r w x : α → Nat)
    (h : ∀ i ∈ xs,l i+18*r i+6*(x i%2) ≤ 28+30*w i+6*x i) :
    total xs l+18*total xs r+6*total xs (fun i => x i%2) ≤
    28*xs.length+30*total xs w+6*total xs x := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    have head := h a (by simp)
    have tail := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [total_cons,List.length_cons]; omega

private theorem parity {α} (xs : List α) (g : α → Nat) :
    (total xs g)%2=(total xs (fun i => g i%2))%2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [total_cons]; omega

private theorem indicator {α} (xs : List α) (p : α → Bool) :
    total xs (fun i => if p i then 1 else 0)=(xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [total_cons,h,ih,Nat.add_comm]

private theorem many {α} (xs : List α) (n : α→Nat) :
    2*xs.length ≤ total xs n+2*(xs.filter (fun i => n i ≤ 1)).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : n a ≤ 1 <;> simp [total_cons,h] <;> omega

def fails (f : C→V→V) (i : Fin 280) :=
  (colors.filter (fun c => (shadow (matching (f c))).testBit i.val)).length

/-- On every eligible initial split, at least ten of the 280 ways to finish
connect at least fourteen colors. The point names fix the initial split to
012 and 345. An arbitrary naming of the vertices can be used. -/
theorem ten_near (f : C → V → V) (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (cover : ∀ x y : V, x≠y → ∃ c, f c x=y)
    (sparse : ∀ c, count 32831 (matching (f c))≤2)
    (eligible : ∀ c, count 32775 (matching (f c))≠2 ∧ count 32824 (matching (f c))≠2) :
    10 ≤ (indices.filter (fun i => fails f i≤1)).length ∧
    ∀ i : Fin 280, fails f i≤1 →
      ∃ cs : List C, cs.Nodup ∧ 14≤cs.length ∧ ∀ c∈cs,
        Connected (Adj (wild (atLayout i) ++ actualEdges (f c))) := by
  let m c := matching (f c)
  have account (c) : accounting (m c)=true := follows accounting _ (inv c) (ne c) 16 points []
    (by decide) (fun _ _ => (by decide : ∀ x : V, x∈points) _) all_totals
  have h (c) := of_decide_eq_true (account c)
  have tr : total colors (fun c => rcount (m c))=6 := by
    have eq (c) : rcount (m c)=tally (m c) rootEdges := (h c).1.symm
    simp only [eq]; exact tally_total _ (by decide) f inv ne proper cover
  have tw : total colors (fun c => wcount (m c))=6 := by
    have eq (c) : wcount (m c)=tally (m c) withinEdges := (h c).2.1.symm
    simp only [eq]; exact tally_total _ (by decide) f inv ne proper cover
  have tx : total colors (fun c => xcount (m c))=9 := by
    have eq (c) : xcount (m c)=tally (m c) acrossEdges := (h c).2.2.1.symm
    simp only [eq]; exact tally_total _ (by decide) f inv ne proper cover
  have sum := sum_price colors (fun c => badCount (shadow (m c))) (fun c => rcount (m c))
    (fun c => wcount (m c)) (fun c => xcount (m c)) (fun c _ => lam_price _ (inv c) (ne c) _ rfl
      (sparse c) (eligible c).1 (eligible c).2 ⟨(h c).2.2.2.1,(h c).2.2.2.2.1⟩ (h c).2.2.2.2.2)
  have odd := parity colors (fun c => xcount (m c))
  rw [tr,tw,tx,show colors.length=15 by decide] at sum
  rw [tx] at odd
  change (9:Nat)%2 = (total colors (fun i => xcount (m i)%2))%2 at odd
  change total colors (fun c => badCount (shadow (m c))) + 18*6 + 6*total colors (fun i => xcount (m i)%2) ≤ 28*15+30*6+6*9 at sum
  have totalBound : total colors (fun c => badCount (shadow (m c)))≤540 := by omega
  have flip : total indices (fails f) = total colors (fun c => badCount (shadow (m c))) := by
    unfold fails badCount
    simp only [←indicator]
    exact Teams.transpose _ _ _
  have enough := many indices (fails f)
  rw [flip,show indices.length=280 by decide] at enough
  refine ⟨by omega,?_⟩
  intro i hi
  let clear (c : C) := !(shadow (m c)).testBit i.val
  refine ⟨colors.filter clear,(by decide : colors.Nodup).filter _,?_,?_⟩
  · have partition : (colors.filter clear).length+fails f i=colors.length := by
      have part {α : Type} (xs : List α) (p : α → Bool) :
          (xs.filter (fun x => !p x)).length+(xs.filter p).length=xs.length := by
        induction xs with
        | nil => rfl
        | cons x xs ih => cases h : p x <;> simp [h,ih,Nat.succ_add] <;> omega
      exact part colors _
    rw [show colors.length=15 by decide] at partition
    omega
  · intro c hc
    exact connects _ (inv c) (ne c) i (by simpa [clear,m] using (List.mem_filter.mp hc).2)
#print axioms ten_near
end SevenProfile
