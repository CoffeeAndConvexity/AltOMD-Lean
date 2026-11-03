import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.NormNum

/-!
# Absolutely summable real power series

For a positive radius `r`, store the weighted coefficients `a n * (r : ℝ) ^ n`
in `ℓ¹`. The coefficient map below identifies this complete space with exactly
the real series of finite weighted coefficient norm. Multiplication is the
Cauchy product, not pointwise multiplication of coefficients.

In the manuscript's completeness proof, the sequence of whole series `P^{[n]}`
is represented by `u : ℕ → Series r`. Its scalar coefficients `a_{n,j}` are
`coeff r (u n) j`. The limit series `P_∞` is represented by `P_lim : Series r`,
with limiting coefficients `a_j = coeff r P_lim j`. The weighted coordinate `(u n) j` is
`a_{n,j} * (r : ℝ) ^ j`.

Completeness is inherited from `ℓ¹`; the manuscript's notation change does not
alter this proof. `dist_eq_weighted_sum` identifies the Lean distance with the
weighted coefficient distance used in that argument.
-/

open scoped BigOperators ENNReal
open Finset

namespace AltOMD.WeightedSeries

/-- The positive radii on which the manuscript defines its weighted series space. -/
abbrev Radius := {r : ℝ // 0 < r}

/-- Weighted coefficients of a real series at a fixed positive radius. -/
abbrev Series (_r : Radius) := lp (fun _ : ℕ => ℝ) 1

variable {r : Radius}

/-- The unweighted scalar coefficient of a whole series `P`.
For a sequence `u : ℕ → Series r`, `coeff r (u n) j` is the manuscript's `a_{n,j}`. -/
noncomputable def coeff (r : Radius) (P : Series r) (n : ℕ) : ℝ := P n / (r : ℝ) ^ n

/-- Completeness of the weighted coefficient space, inherited from `ℓ¹`. -/
theorem completeSpace (r : Radius) : CompleteSpace (Series r) := inferInstance

theorem summable_norm (P : Series r) : Summable (fun n => ‖P n‖) := by
  simpa using (lp.memℓp P).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem norm_eq_tsum (P : Series r) : ‖P‖ = ∑' n, ‖P n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) P

theorem abs_coeff_mul_pow (P : Series r) (n : ℕ) :
    |coeff r P n| * (r : ℝ) ^ n = ‖P n‖ := by
  simp [coeff, abs_div, abs_of_pos (pow_pos r.property n), Real.norm_eq_abs,
    div_mul_cancel₀ _ (pow_ne_zero n r.property.ne')]

theorem summable_coeff (P : Series r) :
    Summable (fun n => |coeff r P n| * (r : ℝ) ^ n) := by
  simpa only [abs_coeff_mul_pow] using summable_norm P

theorem norm_eq_weighted_sum (P : Series r) :
    ‖P‖ = ∑' n, |coeff r P n| * (r : ℝ) ^ n := by
  simp only [abs_coeff_mul_pow, norm_eq_tsum]

/-- The coefficient map respects differences of series. -/
theorem coeff_sub (P Q : Series r) (n : ℕ) :
    coeff r (P - Q) n = coeff r P n - coeff r Q n := by
  change (P n - Q n) / (r : ℝ) ^ n = P n / (r : ℝ) ^ n - Q n / (r : ℝ) ^ n
  exact sub_div _ _ _

/-- The stored distance is exactly the source weighted coefficient distance. -/
theorem dist_eq_weighted_sum (P Q : Series r) :
    dist P Q = ∑' n, |coeff r P n - coeff r Q n| * (r : ℝ) ^ n := by
  rw [dist_eq_norm, norm_eq_weighted_sum (r := r)]
  simp only [coeff_sub]

/-- Every sequence with finite weighted coefficient sum defines a series. -/
noncomputable def ofCoefficients (r : Radius) (a : ℕ → ℝ)
    (ha : Summable (fun n => |a n| * (r : ℝ) ^ n)) : Series r :=
  ⟨fun n => a n * (r : ℝ) ^ n, memℓp_gen (by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos r.property] using ha)⟩

@[simp] theorem coeff_ofCoefficients (a : ℕ → ℝ)
    (ha : Summable (fun n => |a n| * (r : ℝ) ^ n)) (n : ℕ) :
    coeff r (ofCoefficients r a ha) n = a n := by
  simp [coeff, ofCoefficients, pow_ne_zero _ r.property.ne']

@[simp] theorem ofCoefficients_coeff (P : Series r) :
    ofCoefficients r (coeff r P) (summable_coeff P) = P := by
  apply Subtype.ext
  funext n
  simp [ofCoefficients, coeff, pow_ne_zero _ r.property.ne']

theorem coeff_bound (P : Series r) (n : ℕ) :
    |coeff r P n| ≤ (r : ℝ)⁻¹ ^ n * ‖P‖ := by
  rw [inv_pow, ← div_eq_inv_mul]
  apply (le_div_iff₀ (pow_pos r.property n)).2
  rw [abs_coeff_mul_pow]
  exact lp.norm_apply_le_norm (by norm_num) P n

/-- Cauchy multiplication in weighted coordinates. -/
noncomputable def mul (P Q : Series r) : Series r :=
  ⟨fun n => ∑ ij ∈ Finset.antidiagonal n, P ij.1 * Q ij.2,
    memℓp_gen (by
      simpa using summable_norm_sum_mul_antidiagonal_of_summable_norm
        (summable_norm P) (summable_norm Q))⟩

theorem coeff_mul (P Q : Series r) (n : ℕ) :
    coeff r (mul P Q) n =
      ∑ ij ∈ Finset.antidiagonal n, coeff r P ij.1 * coeff r Q ij.2 := by
  unfold coeff mul
  change (∑ ij ∈ Finset.antidiagonal n, P ij.1 * Q ij.2) / (r : ℝ) ^ n = _
  rw [sum_div]
  apply sum_congr rfl
  intro ij hij
  have hn := Finset.mem_antidiagonal.mp hij
  rw [← hn, pow_add, mul_div_mul_comm]

theorem norm_mul_le (P Q : Series r) : ‖mul P Q‖ ≤ ‖P‖ * ‖Q‖ := by
  rw [norm_eq_tsum, norm_eq_tsum P, norm_eq_tsum Q]
  -- Rearrange the nonnegative product series by antidiagonals,
  -- as justified by Tonelli's theorem in the manuscript.
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (by simpa using summable_norm P) (by simpa using summable_norm Q)]
  apply Summable.tsum_le_tsum
  · intro n
    change ‖∑ ij ∈ Finset.antidiagonal n, P ij.1 * Q ij.2‖ ≤ _
    calc
      _ ≤ ∑ ij ∈ Finset.antidiagonal n, ‖P ij.1 * Q ij.2‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  · exact summable_norm (mul P Q)
  · exact (summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => ‖P n‖) (g := fun n => ‖Q n‖)
      (by simpa using summable_norm P) (by simpa using summable_norm Q)).of_norm

/-- The scalar analytic series with the unweighted coefficients. -/
noncomputable def powerSeries (r : Radius) (P : Series r) :
    FormalMultilinearSeries ℝ ℝ ℝ := .ofScalars ℝ (coeff r P)

/-- The analytic series represents the ordinary scalar power-series sum. -/
theorem sum_eq (P : Series r) (t : ℝ) :
    (powerSeries r P).sum t = ∑' n, coeff r P n * t ^ n := by
  simpa only [powerSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (coeff r P) t)

theorem radius_pos (P : Series r) : 0 < (powerSeries r P).radius := by
  have hsum : Summable (fun n => ‖powerSeries r P n‖ * (r : ℝ) ^ n) := by
    simpa [powerSeries, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
      using summable_coeff P
  have hle := (powerSeries r P).le_radius_of_summable_norm (r := ⟨r, r.property.le⟩) hsum
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr r.property) hle

/-- The coefficient norm guarantees an actual analytic sum near zero. -/
theorem hasFPowerSeriesAt (P : Series r) :
    HasFPowerSeriesAt (powerSeries r P).sum (powerSeries r P) 0 :=
  ((powerSeries r P).hasFPowerSeriesOnBall (radius_pos P)).hasFPowerSeriesAt

theorem iteratedDeriv_eq (P : Series r) (n : ℕ) :
    iteratedDeriv n (powerSeries r P).sum 0 = (n.factorial : ℝ) * coeff r P n := by
  have h := ((powerSeries r P).hasFPowerSeriesOnBall (radius_pos P)).factorial_smul 1 n
  simpa [iteratedDeriv_eq_iteratedFDeriv, powerSeries,
    FormalMultilinearSeries.ofScalars, nsmul_eq_mul] using h.symm

/-- The manuscript's derivative estimate, including derivative order zero. -/
theorem abs_iteratedDeriv_le (P : Series r) (n : ℕ) :
    |iteratedDeriv n (powerSeries r P).sum 0| ≤
      (n.factorial : ℝ) * (r : ℝ)⁻¹ ^ n * ‖P‖ := by
  rw [iteratedDeriv_eq, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (coeff_bound P n) (Nat.cast_nonneg _)

end AltOMD.WeightedSeries
