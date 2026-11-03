import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Exponential

/-! Finite truncation estimates for the modified Hamiltonian. -/

namespace AltOMD

open Finset

lemma remainder_weight_sum_le_exp (N : ℕ) :
    (∑ r ∈ range (N + 1), (2 : ℝ) ^ (N + 2 - r) /
      ((N + 2 - r).factorial : ℝ)) ≤ Real.exp 2 := by
  calc
    _ ≤ ∑ r ∈ range (N + 3), (2 : ℝ) ^ (N + 2 - r) /
        ((N + 2 - r).factorial : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro r hr hn
      positivity
    _ = ∑ r ∈ range (N + 3), (2 : ℝ) ^ r / (r.factorial : ℝ) := by
      simpa only [show N + 3 - 1 = N + 2 by omega] using
        sum_range_reflect (fun r => (2 : ℝ) ^ r / (r.factorial : ℝ)) (N + 3)
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) (N + 3)

/-- A finite geometric estimate expressed using consecutive-term bounds. -/
lemma sum_le_twice_first (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ r, 0 ≤ a r) (hratio : ∀ r < N, 2 * a (r + 2) ≤ a (r + 1)) :
    ∑ r ∈ range N, a (r + 1) ≤ 2 * a 1 := by
  have aux : ∀ n ≤ N, (∑ r ∈ range n, a (r + 1)) + 2 * a (n + 1) ≤ 2 * a 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hr := hratio n (by omega)
      rw [sum_range_succ]
      have he : n + 1 + 1 = n + 2 := by omega
      rw [he]
      linarith
  have h := aux N le_rfl
  linarith [ha (N + 1)]

/-- Consecutive terms bounded by a quarter of their predecessor sum to at most
four thirds of the first term. -/
lemma sum_le_four_thirds_first (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ r, 0 ≤ a r) (hratio : ∀ r < N, 4 * a (r + 2) ≤ a (r + 1)) :
    ∑ r ∈ range N, a (r + 1) ≤ (4 / 3 : ℝ) * a 1 := by
  have aux : ∀ n ≤ N,
      3 * (∑ r ∈ range n, a (r + 1)) + 4 * a (n + 1) ≤ 4 * a 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hr := hratio n (by omega)
      rw [sum_range_succ]
      have he : n + 1 + 1 = n + 2 := by omega
      rw [he]
      linarith
  have h := aux N le_rfl
  linarith [ha (N + 1)]

noncomputable def correctionBound (C η : ℝ) (r : ℕ) : ℝ :=
  η ^ r * (4 * C) ^ (r + 1) * (r.factorial : ℝ)

lemma correctionBound_succ (C η : ℝ) (r : ℕ) :
    correctionBound C η (r + 1) = correctionBound C η r * (η * (4 * C) * (r + 1)) := by
  simp only [correctionBound, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  ring

/-- The factorial growth is dominated by the chosen step size up to the
truncation order. -/
theorem correction_sum_bound {C η : ℝ} (N : ℕ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hsmall : 16 * C * η * (N + 2) ≤ 1) :
    ∑ r ∈ range N, correctionBound C η (r + 1) ≤ (64 / 3 : ℝ) * C ^ 2 * η := by
  have hnonneg : ∀ r, 0 ≤ correctionBound C η r := by
    intro r
    unfold correctionBound
    positivity
  have hratio : ∀ r < N,
      4 * correctionBound C η (r + 2) ≤ correctionBound C η (r + 1) := by
    intro r hr
    rw [show r + 2 = (r + 1) + 1 by omega, correctionBound_succ]
    have hindex : (r : ℝ) + 2 ≤ (N : ℝ) + 2 := by
      have hi : (r : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hr)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hindex
      (show 0 ≤ η * (4 * C) by positivity)
    have hfac : 4 * (η * (4 * C) * ((r + 1 : ℕ) + 1)) ≤ 1 := by
      push_cast
      nlinarith
    have := mul_le_mul_of_nonneg_left hfac (hnonneg (r + 1))
    nlinarith
  have h := sum_le_four_thirds_first (correctionBound C η) N hnonneg hratio
  convert h using 1 <;> simp [correctionBound] <;> ring

noncomputable def truncatedEnergy {E : Type*} (H : ℕ → E → ℝ)
    (N : ℕ) (η : ℝ) (z : E) : ℝ :=
  H 0 z + ∑ r ∈ range N, η ^ (r + 1) * H (r + 1) z

/-- Uniform coefficient bounds imply closeness of the finite modified energy.
This lemma makes no convergence assumption on the formal series. -/
theorem truncatedEnergy_close {E : Type*} (H : ℕ → E → ℝ)
    (N : ℕ) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hsmall : 16 * C * η * (N + 2) ≤ 1)
    (hcoeff : ∀ r < N, ∀ z, |H (r + 1) z| ≤
      (4 * C) ^ (r + 2) * ((r + 1).factorial : ℝ)) (z : E) :
    |truncatedEnergy H N η z - H 0 z| ≤ (64 / 3 : ℝ) * C ^ 2 * η := by
  unfold truncatedEnergy
  rw [add_sub_cancel_left]
  calc
    |∑ r ∈ range N, η ^ (r + 1) * H (r + 1) z| ≤
        ∑ r ∈ range N, |η ^ (r + 1) * H (r + 1) z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ range N, correctionBound C η (r + 1) := by
      apply sum_le_sum
      intro r hr
      rw [abs_mul, abs_pow, abs_of_nonneg hη]
      have hb := mul_le_mul_of_nonneg_left (hcoeff r (mem_range.mp hr) z)
        (pow_nonneg hη (r + 1))
      simpa [correctionBound, mul_assoc, Nat.add_assoc] using hb
    _ ≤ _ := correction_sum_bound N hC hη hsmall

lemma factorial_succ_le_pow (n : ℕ) : (n + 1).factorial ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ]
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul_right
    exact ih.trans (Nat.pow_le_pow_left (by omega) n)

/-- The selected truncation order turns a factorial Taylor remainder into an
exponentially small defect. -/
theorem factorial_defect_bound {C η : ℝ} (N : ℕ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hsmall : 16 * C * η * (N + 2) ≤ 1) :
    Real.exp 2 * η ^ (N + 2) * (4 * C) ^ (N + 3) * ((N + 2).factorial : ℝ) ≤
      16 * Real.exp 2 * C ^ 2 * η / (4 : ℝ) ^ (N + 1) := by
  have hfac : ((N + 2).factorial : ℝ) ≤ ((N : ℝ) + 2) ^ (N + 1) := by
    exact_mod_cast factorial_succ_le_pow (N + 1)
  have hsmall' : 0 ≤ 4 * C * η * ((N : ℝ) + 2) := by positivity
  have hsmall'' : 4 * C * η * ((N : ℝ) + 2) ≤ (1 / 4 : ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ hsmall' hsmall'' (N + 1)
  calc
    _ ≤ Real.exp 2 * η ^ (N + 2) * (4 * C) ^ (N + 3) *
        ((N : ℝ) + 2) ^ (N + 1) := by gcongr
    _ = 16 * Real.exp 2 * C ^ 2 * η *
        (4 * C * η * ((N : ℝ) + 2)) ^ (N + 1) := by
      simp only [mul_pow, show N + 2 = (N + 1) + 1 by omega,
        show N + 3 = (N + 1) + 1 + 1 by omega, pow_succ]
      ring
    _ ≤ 16 * Real.exp 2 * C ^ 2 * η * (1 / 4 : ℝ) ^ (N + 1) := by
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 16 * Real.exp 2 * C ^ 2 * η / (4 : ℝ) ^ (N + 1) := by
      rw [div_pow, one_pow]
      ring

end AltOMD
