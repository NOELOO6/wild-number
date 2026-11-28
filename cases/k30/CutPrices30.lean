import CutModel30

namespace WildSieve.Thirty
open Finset

/-- Exact dual multipliers for the moments of the three types of two-triple hits. -/
def prices : List (Row × ℚ) :=
  [
    (.mass, 500001/500000),
    (.colors, -145675787241/42542500000000),
    (.leftEdges, -6859/2500000),
    (.product 0 6 2, 925729/100000000),
    (.product 1 6 0, -176609/50000000),
    (.product 2 6 2, 323179/50000000),
    (.mean 2, -185527/500000),
    (.other 2 2, 213817/5000000),
    (.mean 1, -3/5),
    (.other 1 2, 24619/200000),
    (.other 2 1, 290983/10000000),
    (.other 1 1, 133333/1000000),
    (.mean 0, -333333/1000000),
    (.other 0 2, 173333/10000000),
    (.other 2 0, 293817/5000000),
    (.other 0 1, 133333/1000000),
    (.other 0 0, 9527/3125000),
    (.complement, 302847/10000000),
    (.product 0 0 2, 756303/1000000000),
    (.distinct 1, -37224867/100000000),
    (.closing 1 0, -91117/50000000),
    (.product 1 0 2, 321821/50000000),
    (.distinct 2, -267671/1000000),
    (.closing 2 0, 1363/5000000),
    (.product 2 0 2, 361971/100000000),
    (.closing 1 1, 4497/312500000),
    (.product 1 1 2, 1901/781250),
    (.closing 2 1, -14377/25000000),
    (.product 2 1 2, 153041/100000000),
    (.product 0 2 0, -2521/20000000),
    (.closing 1 2, 98051/50000000),
    (.closing 2 2, -18999/12500000),
    (.distinct 0, -32446271369/221000000000),
    (.closing 0 3, 122549/250000000),
    (.closing 1 3, 58837/25000000),
    (.closing 2 3, -306657/100000000),
    (.closing 0 4, 107843/100000000),
    (.closing 1 4, -25543/25000000),
    (.product 1 4 2, 76923/20000000),
    (.closing 2 4, -96509/25000000),
    (.product 2 4 2, 321311/500000000),
    (.closing 0 5, -11859/10000000),
    (.product 0 5 2, 176013/100000000),
    (.closing 1 5, -32259/1250000),
    (.product 1 5 2, 79147/12500000),
    (.closing 2 5, -62433/12500000),
    (.product 2 5 2, 348811/100000000),
    (.closing 0 6, -1949/1250000),
    (.closing 2 6, -392967/100000000),
    (.duplicateColors, 8847/12500000000),
    (.duplicateEdges, 176177/250000000000),
    (.regionalColors 0, 351309813/110500000000),
    (.edges 0 0, 152311/25000000),
    (.edges 0 1, -47619/100000000),
    (.edges 0 2, 252101/500000000),
    (.edges 0 4, 152311/25000000),
    (.edges 0 5, 252101/500000000),
    (.edges 0 7, 798319/1000000000),
    (.anchor 0, -95233/12500000),
    (.regionalColors 1, 122449/20000000),
    (.edges 1 0, 999477/100000000),
    (.edges 1 1, -101583/50000000),
    (.edges 1 2, 30089/25000000),
    (.edges 1 4, 51511/6250000),
    (.edges 1 6, -178179/100000000),
    (.edges 1 7, 90267/50000000),
    (.edges 2 0, 20893/10000000),
    (.edges 2 1, 60967/50000000),
    (.edges 2 3, 428407/500000000),
    (.edges 2 4, 20893/10000000),
    (.edges 2 6, 428407/500000000),
    (.edges 2 8, -11321/25000000),
    (.edges 2 9, 116557/100000000),
    (.regionalColors 2, 9/2750000000)
  ]

def longPrice : ℚ := 1148325713977/1636250000000

def priced (j : Column) := (prices.map fun p => p.2*coeff p.1 j).sum

def compatible (r : Row) (p : ℚ) : Prop :=
  match sense r with
  | .eq => True | .le => 0≤p | .ge => p≤0

instance (r : Row) (p : ℚ) : Decidable (compatible r p) := by
  unfold compatible
  split <;> infer_instance

/-- All 3,520 columns of the primal moment problem are nonnegative after subtracting
the objective. The two edge-count and histogram enumerations are independent. -/
private theorem price_checks :
    (columns.all (fun j => decide (objective j ≤ priced j)) = true) ∧
    (prices.all (fun p => decide (compatible p.1 p.2)) = true) ∧
    (prices.map (fun p => p.2*rhs p.1)).sum = longPrice := by native_decide

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
on the probability of no marked pair, less the duplicate-label allowance. -/
theorem long_certificate (amount : Column → ℚ)
    (nonneg : ∀ j∈columns, 0≤amount j)
    (feasible : ∀ p∈prices, Feasible amount p.1) :
    total amount objective ≤ longPrice := by
  obtain ⟨cols,rows,value⟩ := price_checks
  calc
    total amount objective ≤ total amount priced := sum_mono columns _ _ (fun j hj =>
      mul_le_mul_of_nonneg_right (of_decide_eq_true ((List.all_eq_true.mp cols) j hj)) (nonneg j hj))
    _ = _ := exchange amount prices
    _ ≤ (prices.map (fun p => p.2*rhs p.1)).sum := sum_mono prices _ _ (fun p hp =>
      price_row amount (of_decide_eq_true ((List.all_eq_true.mp rows) p hp)) (feasible p hp))
    _ = longPrice := value

theorem dominates {j : Column} (member : j∈columns) : objective j≤priced j :=
  of_decide_eq_true (List.all_eq_true.mp price_checks.1 j member)

def RowHolds (eval : (Column → ℚ) → ℚ) (r : Row) : Prop :=
  match sense r with
  | .eq => eval (coeff r)=rhs r
  | .le => eval (coeff r)≤rhs r
  | .ge => rhs r≤eval (coeff r)

def indexed : Row → Bool
  | .mean t | .distinct t | .regionalColors t | .anchor t => t<3
  | .edges t k => t<3 && k<10
  | .closing t i => t<3 && i<7
  | .product t i k => t<3 && i<7 && k<4
  | .other t k => t<3 && k<3
  | _ => true

private theorem indexed_prices : prices.all (fun p => indexed p.1)=true := by native_decide

/-- Apply the same exact price certificate directly to a finite graph experiment
given by a positive linear functional on the columns. -/
theorem functional_certificate (eval : (Column → ℚ) → ℚ) (zero : eval (fun _ => 0)=0)
    (linear : ∀ (a : ℚ) f g,eval (fun j => a*f j+g j)=a*eval f+eval g)
    (dom : eval objective≤eval priced) (rows : ∀ r,indexed r=true → RowHolds eval r) :
    eval objective≤longPrice := by
  have exchange' (ps : List (Row × ℚ)) : eval (fun j => (ps.map (fun p => p.2*coeff p.1 j)).sum)=
      (ps.map (fun p => p.2*eval (coeff p.1))).sum := by
    induction ps with
    | nil => simpa using zero
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [linear,ih]
  calc
    eval objective ≤ eval priced := dom
    _ = _ := exchange' prices
    _ ≤ (prices.map fun p => p.2*rhs p.1).sum := by
      apply sum_mono
      intro p hp
      have valid := rows p.1 (List.all_eq_true.mp indexed_prices p hp)
      have sign := of_decide_eq_true (List.all_eq_true.mp price_checks.2.1 p hp)
      unfold compatible at sign
      unfold RowHolds at valid
      cases h : sense p.1 <;> simp only [h] at sign valid
      · rw [valid]
      · exact mul_le_mul_of_nonneg_left valid sign
      · exact mul_le_mul_of_nonpos_left valid sign
    _ = longPrice := price_checks.2.2

#print axioms long_certificate

end WildSieve.Thirty
