import CutModel24

namespace WildSieve.TwentyFour

/-- Dual multipliers for the combined short- and long-cut inequalities. -/
def prices : List (Row × ℚ) :=
  [
    (.mass, 550131/2000000),
    (.colors, 1171477/24062500000000),
    (.product 0 6 2, 68697/50000000),
    (.product 2 6 2, 114383/100000000),
    (.cycleMass, 5275980120585004403/7201285000000000000),
    (.profile 6, -193607/25000000),
    (.mean 2, -26167/250000),
    (.other 2 2, 22113/40000000),
    (.rightComplement, 118609/10000000),
    (.mean 1, -14423/125000),
    (.other 2 1, 55013/2000000),
    (.other 1 1, 155393/10000000),
    (.mean 0, -26167/250000),
    (.other 0 2, 4433/312500),
    (.other 2 0, 106419/10000000),
    (.other 0 1, 55013/2000000),
    (.other 0 0, 22113/40000000),
    (.complement, 118609/10000000),
    (.product 0 0 2, 118433/100000000),
    (.distinct 1, -2996694857/35000000000),
    (.closing 1 0, 403019/1000000000),
    (.product 1 0 0, -132137/5000000000),
    (.product 2 0 2, 12503/12500000),
    (.profile 0, -307959/100000000),
    (.product 0 1 2, 78903/500000000),
    (.closing 1 1, -22133/50000000),
    (.product 1 1 2, 29731/250000000),
    (.product 2 1 2, 427503/10000000000),
    (.profile 1, -330199/100000000),
    (.closing 1 2, -214723/500000000),
    (.profile 2, -250327/100000000),
    (.distinct 0, -293774121/7000000000),
    (.closing 0 3, 697847/10000000000000),
    (.closing 1 3, -6739/20000000),
    (.distinct 2, -3289983273/77000000000),
    (.closing 2 3, 691031/10000000000),
    (.profile 3, -66307/25000000),
    (.closing 0 4, -74983/500000000),
    (.closing 1 4, -22133/50000000),
    (.closing 2 4, -809327/10000000000),
    (.profile 4, -414051/100000000),
    (.closing 0 5, -850133/1000000000),
    (.product 0 5 2, 826473/1000000000),
    (.closing 1 5, -10103/2500000),
    (.product 1 5 2, 132137/5000000000),
    (.closing 2 5, -781099/1000000000),
    (.product 2 5 2, 2367/3125000),
    (.profile 5, -240021/50000000),
    (.closing 0 6, -5401/4000000),
    (.closing 2 6, -64061/50000000),
    (.duplicateColors, 41449/20000000000),
    (.duplicateEdges, 337789/10000000000000),
    (.regionalColors 0, 123/35000000000),
    (.edges 0 0, 17767/10000000),
    (.edges 0 1, 230111/2500000000),
    (.edges 0 2, 61481/125000000),
    (.edges 0 4, 17767/10000000),
    (.edges 0 5, 61481/125000000),
    (.edges 0 7, 174607/250000000),
    (.edges 0 8, 5441/40000000),
    (.regionalColors 1, 747/70000000000),
    (.edges 1 0, 201729/100000000),
    (.edges 1 1, 83687/2000000000),
    (.edges 1 3, 252529/1000000000),
    (.edges 1 4, 3277/2000000),
    (.edges 1 6, -15783/125000000),
    (.edges 1 8, 129201/1000000000),
    (.edges 1 9, 15783/125000000),
    (.regionalColors 2, 457/77000000000),
    (.edges 2 0, 170767/100000000),
    (.edges 2 3, 56687/125000000),
    (.edges 2 4, 170767/100000000),
    (.edges 2 6, 56687/125000000),
    (.edges 2 8, 83353/500000000),
    (.edges 2 9, 345379/500000000),
    (.raw 12, 197/2964500000000),
    (.population 12 55, 52707/500000000),
    (.population 9 255, 421783/10000000000),
    (.population 9 270, 196647/10000000000)
  ]
def lossCap : ℚ := 78926570703464883969/79214135000000000000

def priced (j : Column) := (prices.map fun p => p.2*coeff p.1 j).sum

def compatible (r : Row) (p : ℚ) : Prop :=
  match sense r with
  | .eq => True | .le => 0≤p | .ge => p≤0

instance (r : Row) (p : ℚ) : Decidable (compatible r p) := by
  unfold compatible
  split <;> infer_instance

/-- Check every column, the dual signs and the exact weighted constant. -/
private theorem price_checks :
    (columns.all (fun j => decide (objective j ≤ priced j)) = true) ∧
    (prices.all (fun p => decide (compatible p.1 p.2)) = true) ∧
    (prices.map (fun p => p.2*rhs p.1)).sum = lossCap := by native_decide

def total (amount : Column → ℚ) (f : Column → ℚ) :=
  (columns.map fun j => f j*amount j).sum

def Feasible (amount : Column → ℚ) (r : Row) : Prop :=
  match sense r with
  | .eq => total amount (coeff r) = rhs r
  | .le => total amount (coeff r) ≤ rhs r
  | .ge => rhs r ≤ total amount (coeff r)

private theorem price_row (amount : Column → ℚ) {p : Row × ℚ}
    (hp : compatible p.1 p.2) (hf : Feasible amount p.1) :
    p.2*total amount (coeff p.1) ≤ p.2*rhs p.1 := by
  unfold compatible at hp
  unfold Feasible at hf
  cases h : sense p.1 <;> simp only [h] at hp hf
  · rw [hf]
  · exact mul_le_mul_of_nonneg_left hf hp
  · exact mul_le_mul_of_nonpos_left hf hp

private theorem sum_mono {α : Type} (l : List α) (f g : α → ℚ)
    (h : ∀ a∈l, f a≤g a) : (l.map f).sum≤(l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem total_linear (v : Column → ℚ) (p : ℚ) (f g : Column → ℚ) :
    total v (fun j => p*f j + g j) = p*total v f + total v g := by
  unfold total
  generalize columns = l
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

private theorem exchange (v : Column → ℚ) (ps : List (Row × ℚ)) :
    total v (fun j => (ps.map (fun p => p.2*coeff p.1 j)).sum) =
      (ps.map (fun p => p.2*total v (coeff p.1))).sum := by
  induction ps with
  | nil => simp [total]
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [total_linear,ih]

/-- Every nonnegative measure satisfying the priced rows obeys the asserted bound
on the combined probability of losing a partition. -/
theorem cut_certificate (amount : Column → ℚ)
    (nonneg : ∀ j∈columns, 0≤amount j)
    (feasible : ∀ p∈prices, Feasible amount p.1) :
    total amount objective ≤ lossCap := by
  obtain ⟨cols,rows,value⟩ := price_checks
  calc
    total amount objective ≤ total amount priced := sum_mono columns _ _ (fun j hj =>
      mul_le_mul_of_nonneg_right (of_decide_eq_true ((List.all_eq_true.mp cols) j hj)) (nonneg j hj))
    _ = _ := exchange amount prices
    _ ≤ (prices.map (fun p => p.2*rhs p.1)).sum := sum_mono prices _ _ (fun p hp =>
      price_row amount (of_decide_eq_true ((List.all_eq_true.mp rows) p hp)) (feasible p hp))
    _ = lossCap := value

/-- Rounding the loss bound gives an integer count of surviving partitions. -/
theorem winners_of_loss (bad good : Nat) (total : good+bad=Thirty.triples 8)
    (loss : (bad : ℚ)/(Thirty.triples 8 : ℚ)≤lossCap) : 33258864925≤good := by
  norm_num [Thirty.triples,lossCap,Nat.factorial] at loss total
  by_contra! low
  have : 9128421663076≤bad := by omega
  exact False.elim (by linarith only [loss,show (9128421663076 : ℚ)≤bad by exact_mod_cast this])

#print axioms cut_certificate
#print axioms winners_of_loss
end WildSieve.TwentyFour
