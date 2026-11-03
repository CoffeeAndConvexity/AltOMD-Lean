import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Geometry of the maximizing tuple in Banach's diagonal-norm theorem. -/

namespace AltOMD.Polarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If changing signs and averaging two unit vectors cannot increase the norm
of their sum with the remaining vectors, the two unit vectors coincide. -/
theorem eq_of_norm_sum_max (x y r : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hflipx : ‖r - x + y‖ ≤ ‖r + x + y‖)
    (hflipy : ‖r + x - y‖ ≤ ‖r + x + y‖)
    (hflipboth : ‖r - x - y‖ ≤ ‖r + x + y‖)
    (havg : x + y ≠ 0 →
      ‖r + (2 / ‖x + y‖) • (x + y)‖ ≤ ‖r + x + y‖) : x = y := by
  have hp : x + y ≠ 0 := by
    intro hp
    have hxy : y = -x := eq_neg_of_add_eq_zero_right hp
    have hbase : r + x + y = r := by rw [hxy]; abel
    have hfx : r - x + y = r - (2 : ℝ) • x := by rw [hxy]; module
    have hfy : r + x - y = r + (2 : ℝ) • x := by rw [hxy]; module
    rw [hbase, hfx] at hflipx
    rw [hbase, hfy] at hflipy
    have hx2 := norm_smul (2 : ℝ) x
    norm_num [hx] at hx2
    have h₁ := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hflipx
    have h₂ := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hflipy
    rw [norm_sub_sq_real, hx2] at h₁
    rw [norm_add_sq_real, hx2] at h₂
    nlinarith
  have hp_pos : 0 < ‖x + y‖ := norm_pos_iff.mpr hp
  have hp_le : ‖x + y‖ ≤ 2 := by
    simpa only [hx, hy, one_add_one_eq_two] using norm_add_le x y
  have hinner : 0 ≤ inner ℝ r (x + y) := by
    have hboth : r - x - y = r - (x + y) := by abel
    have hbase : r + x + y = r + (x + y) := by abel
    rw [hboth, hbase] at hflipboth
    have h := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hflipboth
    rw [norm_sub_sq_real r (x + y), norm_add_sq_real r (x + y)] at h
    linarith
  have ha : 1 ≤ 2 / ‖x + y‖ := (le_div_iff₀ hp_pos).2 (by simpa using hp_le)
  have havg' := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 (havg hp)
  have hbase : r + x + y = r + (x + y) := by abel
  rw [hbase, norm_add_sq_real r ((2 / ‖x + y‖) • (x + y)),
    norm_add_sq_real r (x + y), norm_smul, real_inner_smul_right] at havg'
  have hnorm : ‖(2 : ℝ) / ‖x + y‖‖ * ‖x + y‖ = 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hp_pos)]
    exact div_mul_cancel₀ _ hp_pos.ne'
  rw [hnorm] at havg'
  have hscale : inner ℝ r (x + y) ≤
      (2 / ‖x + y‖) * inner ℝ r (x + y) :=
    le_mul_of_one_le_left hinner ha
  have heq : ‖x + y‖ = ‖x‖ + ‖y‖ := by
    rw [hx, hy]
    nlinarith [norm_nonneg (x + y)]
  simpa [hx, hy] using norm_add_eq_iff_real.mp heq

end AltOMD.Polarization
