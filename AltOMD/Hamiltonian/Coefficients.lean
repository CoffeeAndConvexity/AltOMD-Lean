import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Elementary scalar bounds for BCH coefficient mass

These estimates bound the factorial coefficients in the product of two
exponentials, the scalar logarithm weights, and the normalization by degree.
`WordCoefficients` uses them to bound the mass of the explicit word expansion.
-/

namespace AltOMD
namespace Coefficients

open scoped BigOperators

noncomputable section

/-- Total coefficient mass in degree `n` of a product of two exponentials. -/
def exponentialMass (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), 1 / ((j.factorial : ℝ) * ((n - j).factorial : ℝ))

theorem exponentialMass_eq (n : ℕ) : exponentialMass n = 2 ^ n / (n.factorial : ℝ) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      1 / ((j.factorial : ℝ) * ((n - j).factorial : ℝ)) =
        (n.choose j : ℝ) / (n.factorial : ℝ) := by
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hchoose : (n.choose j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ) =
        (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
    have hfac (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    apply (div_eq_div_iff (mul_ne_zero (hfac j) (hfac (n - j))) (hfac n)).2
    simpa [mul_assoc] using hchoose.symm
  unfold exponentialMass
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  exact_mod_cast Nat.sum_range_choose n

theorem exponentialMass_le (n : ℕ) : exponentialMass n ≤ 2 ^ n := by
  rw [exponentialMass_eq]
  have hfac : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  exact div_le_self (by positivity) hfac

/-- The absolute value of the scalar coefficient in `log(1+E)`. -/
theorem log_weight_le (k : ℕ) : |(-1 : ℝ) ^ (k + 1) / (k : ℝ)| ≤ 1 := by
  cases k with
  | zero => simp
  | succ k =>
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    simp only [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
    exact div_le_self (by norm_num) hk

/-- Dividing by degree in the Dynkin--Specht--Wever projection does not
increase the coefficient mass. -/
theorem dsw_mass_bound {q : ℕ} (hq : 1 ≤ q) {mass : ℝ}
    (hmass : 0 ≤ mass) (hbound : mass ≤ (4 : ℝ) ^ q) :
    mass / (q : ℝ) ≤ (4 : ℝ) ^ q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  exact (div_le_self hmass hqR).trans hbound

/-- The coefficient bound at the shifted Hamiltonian index `q=r+1`. -/
theorem correction_mass_bound (r : ℕ) {mass : ℝ}
    (hmass : 0 ≤ mass) (hbound : mass ≤ (4 : ℝ) ^ (r + 1)) :
    mass / ((r + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (r + 1) :=
  dsw_mass_bound (by omega) hmass hbound

end
end Coefficients
end AltOMD
