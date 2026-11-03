import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import AltOMD.Hamiltonian.Coefficients

/-! Scalar Taylor estimates with the exact factorial remainder. -/

open scoped ContDiff
open Finset Set

namespace AltOMD

noncomputable def taylorPolynomial (f : ℝ → ℝ) (m : ℕ) (h : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1), h ^ k / (k.factorial : ℝ) * iteratedDeriv k f 0

lemma taylorPolynomial_eq_within (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) {h : ℝ} (hh : h ≠ 0) :
    taylorPolynomial f m h = taylorWithinEval f m (uIcc 0 h) 0 h := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hh))
    (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)) (left_mem_uIcc)]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- A uniform bound on the actual `(m+1)`st derivative controls the scalar
Taylor remainder by `M h^(m+1)/(m+1)!`. -/
theorem taylor_remainder_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ t ∈ Icc 0 h, |iteratedDeriv (m + 1) f t| ≤ M) :
    |f h - taylorPolynomial f m h| ≤ M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hh with rfl | hh
  · simp [taylorPolynomial, Finset.sum_range_succ', iteratedDeriv_zero]
  · rw [taylorPolynomial_eq_within f hf m (ne_of_gt hh)]
    obtain ⟨t, ht, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (ne_of_lt hh) (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (m + 1))).contDiffOn
    rw [uIoo_of_lt hh] at ht
    rw [heq, abs_div, abs_mul, sub_zero, abs_pow,
      abs_of_nonneg hh.le,
      abs_of_nonneg (show (0 : ℝ) ≤ ((m + 1).factorial : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hM t ⟨ht.1.le, ht.2.le⟩) (pow_nonneg hh.le _))
      (Nat.cast_nonneg _)

/-- The two successive Taylor remainders have the binomial total weight. -/
lemma split_taylor_weight (m : ℕ) (M h : ℝ) :
    M * h ^ (m + 1) / ((m + 1).factorial : ℝ) +
      (∑ k ∈ range (m + 1), h ^ k / (k.factorial : ℝ) *
        (M * h ^ (m - k + 1) / ((m - k + 1).factorial : ℝ))) =
      2 ^ (m + 1) * M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hterm (k : ℕ) (hk : k ≤ m + 1) :
      h ^ k / (k.factorial : ℝ) *
        (M * h ^ (m + 1 - k) / ((m + 1 - k).factorial : ℝ)) =
      (1 / ((k.factorial : ℝ) * ((m + 1 - k).factorial : ℝ))) *
        (M * h ^ (m + 1)) := by
    rw [show h ^ (m + 1) = h ^ k * h ^ (m + 1 - k) by
      rw [← pow_add, Nat.add_sub_of_le hk]]
    ring
  have hsum : (∑ k ∈ range (m + 2), h ^ k / (k.factorial : ℝ) *
      (M * h ^ (m + 1 - k) / ((m + 1 - k).factorial : ℝ))) =
      2 ^ (m + 1) * M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
    calc
      _ = (∑ k ∈ range (m + 2),
          1 / ((k.factorial : ℝ) * ((m + 1 - k).factorial : ℝ))) *
          (M * h ^ (m + 1)) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro k hk
        exact hterm k (by have := mem_range.mp hk; omega)
      _ = _ := by
        change Coefficients.exponentialMass (m + 1) * _ = _
        rw [Coefficients.exponentialMass_eq]
        ring
  rw [show m + 2 = (m + 1) + 1 by omega, sum_range_succ] at hsum
  simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    div_one] at hsum
  have hs : (∑ k ∈ range (m + 1), h ^ k / (k.factorial : ℝ) *
      (M * h ^ (m - k + 1) / ((m - k + 1).factorial : ℝ))) =
      ∑ k ∈ range (m + 1), h ^ k / (k.factorial : ℝ) *
      (M * h ^ (m + 1 - k) / ((m + 1 - k).factorial : ℝ)) := by
    apply sum_congr rfl
    intro k hk
    rw [show m - k + 1 = m + 1 - k by have := mem_range.mp hk; omega]
  rw [hs]
  convert hsum using 1 <;> ring

end AltOMD
