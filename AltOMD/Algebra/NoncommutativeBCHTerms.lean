import AltOMD.Algebra.NoncommutativeRescale
import Mathlib.Tactic.Module

/-!
# The initial coefficients of the formal BCH series

These exact identities provide the base cases for the all-degree
Lie-membership induction. They hold in arbitrary rational algebras.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

omit [Algebra ℚ A] in
private theorem coeff_mul_one (p q : PowerSeries A) :
    PowerSeries.coeff 1 (p * q) =
      p.constantCoeff * PowerSeries.coeff 1 q + PowerSeries.coeff 1 p * q.constantCoeff := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

omit [Algebra ℚ A] in
private theorem coeff_mul_two (p q : PowerSeries A) :
    PowerSeries.coeff 2 (p * q) =
      p.constantCoeff * PowerSeries.coeff 2 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 1 q +
          PowerSeries.coeff 2 p * q.constantCoeff := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_expOf_one (p : PowerSeries A) :
    PowerSeries.coeff 1 (expOf p) = PowerSeries.coeff 1 p := by
  rw [coeff_expOf]
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_one]

theorem coeff_expOf_two {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    PowerSeries.coeff 2 (expOf p) = PowerSeries.coeff 2 p +
      (1 / 2 : ℚ) • (PowerSeries.coeff 1 p * PowerSeries.coeff 1 p) := by
  rw [coeff_expOf]
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_one, pow_two, coeff_mul_two, hp]

theorem coeff_logOf_one (u : PowerSeries A) :
    PowerSeries.coeff 1 (logOf u) = PowerSeries.coeff 1 u := by
  rw [coeff_logOf]
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_one]

theorem coeff_logOf_two {u : PowerSeries A} (hu : u.constantCoeff = 1) :
    PowerSeries.coeff 2 (logOf u) = PowerSeries.coeff 2 u -
      (1 / 2 : ℚ) • (PowerSeries.coeff 1 u * PowerSeries.coeff 1 u) := by
  rw [coeff_logOf]
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_one, pow_two,
    coeff_mul_two, hu, sub_eq_add_neg]

@[simp] theorem bchCoefficient_zero (a b : A) : bchCoefficient 0 a b = 0 := by
  simp [bchCoefficient, PowerSeries.coeff_zero_eq_constantCoeff_apply]

@[simp] theorem bchCoefficient_one (a b : A) : bchCoefficient 1 a b = a + b := by
  simp [bchCoefficient, bch, coeff_logOf_one, coeff_mul_one,
    coeff_expOf_one, add_comm]

/-- The quadratic BCH coefficient is one half of the commutator. -/
theorem bchCoefficient_two (a b : A) :
    bchCoefficient 2 a b = (1 / 2 : ℚ) • (a * b - b * a) := by
  unfold bchCoefficient bch
  rw [coeff_logOf_two (by simp), coeff_mul_two, coeff_mul_one]
  simp only [constantCoeff_expOf, one_mul, mul_one, coeff_expOf_one,
    coeff_expOf_two (constantCoeff_monomial_one a),
    coeff_expOf_two (constantCoeff_monomial_one b)]
  norm_num [PowerSeries.coeff_monomial]
  simp only [mul_add, add_mul, smul_add, smul_sub]
  module

end
end AltOMD.NoncommutativeSeries
