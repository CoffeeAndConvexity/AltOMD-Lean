import AltOMD.Entropy.Polarization
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Pair averaging at a norm-attaining tuple, used in Banach's theorem. -/

open Finset Function
open scoped BigOperators

namespace AltOMD.Polarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- Replace two coordinates of a tuple. -/
def pairUpdate (v : Fin n → E) (i j : Fin n) (x y : E) : Fin n → E :=
  Function.update (Function.update v i x) j y

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem pairUpdate_comm (v : Fin n → E) {i j : Fin n} (hij : i ≠ j)
    (x y : E) : pairUpdate v i j x y = pairUpdate v j i y x :=
  by simpa only [pairUpdate] using (Function.update_comm hij x y v)

private theorem pairEval_add_right (M : E [×n]→L[ℝ] ℝ) (v : Fin n → E)
    (i j : Fin n) (x y z : E) :
    M (pairUpdate v i j x (y + z)) =
      M (pairUpdate v i j x y) + M (pairUpdate v i j x z) :=
  M.map_update_add _ _ _ _

private theorem pairEval_add_left (M : E [×n]→L[ℝ] ℝ) (v : Fin n → E)
    {i j : Fin n} (hij : i ≠ j) (x y z : E) :
    M (pairUpdate v i j (x + y) z) =
      M (pairUpdate v i j x z) + M (pairUpdate v i j y z) := by
  simp only [pairUpdate_comm v hij, pairEval_add_right]

private theorem pairEval_smul_right (M : E [×n]→L[ℝ] ℝ) (v : Fin n → E)
    (i j : Fin n) (c : ℝ) (x y : E) :
    M (pairUpdate v i j x (c • y)) = c * M (pairUpdate v i j x y) :=
  M.map_update_smul _ _ _ _

private theorem pairEval_smul_left (M : E [×n]→L[ℝ] ℝ) (v : Fin n → E)
    {i j : Fin n} (hij : i ≠ j) (c : ℝ) (x y : E) :
    M (pairUpdate v i j (c • x) y) = c * M (pairUpdate v i j x y) := by
  simp only [pairUpdate_comm v hij, pairEval_smul_right]

private theorem pairEval_swap (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    (v : Fin n → E) {i j : Fin n} (hij : i ≠ j) (x y : E) :
    M (pairUpdate v i j x y) = M (pairUpdate v i j y x) := by
  have heq : pairUpdate v i j x y ∘ Equiv.swap i j = pairUpdate v i j y x := by
    funext k
    by_cases hi : k = i
    · subst k
      simp [pairUpdate, hij]
    by_cases hj : k = j
    · subst k
      simp [pairUpdate, hij]
    simp [pairUpdate, hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]
  rw [← heq, hM]

private theorem pairEval_norm_bound (M : E [×n]→L[ℝ] ℝ)
    (v : Fin n → E) (hv : ∀ k, ‖v k‖ = 1) {i j : Fin n} (hij : i ≠ j) (x y : E) :
    |M (pairUpdate v i j x y)| ≤ ‖M‖ * (‖x‖ * ‖y‖) := by
  have hp : (∏ k, ‖pairUpdate v i j x y k‖) = ‖x‖ * ‖y‖ := by
    have hnorm : (fun k => ‖pairUpdate v i j x y k‖) =
        Function.update (Function.update (fun k => ‖v k‖) i ‖x‖) j ‖y‖ := by
      funext k
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [pairUpdate, hi, hj, hij]
    rw [hnorm, Finset.prod_update_of_mem (Finset.mem_univ j)]
    have he : (∏ k ∈ Finset.univ.erase j, Function.update (fun k => ‖v k‖) i ‖x‖ k) = ‖x‖ := by
      rw [Finset.prod_update_of_mem (by simp [hij])]
      simp [hv]
    simp only [Finset.sdiff_singleton_eq_erase, he, mul_comm]
  simpa only [Real.norm_eq_abs, hp] using M.le_opNorm (pairUpdate v i j x y)

/-- Averaging two distinct unit coordinates of a norm-attaining tuple preserves
norm attainment, after normalization, provided their sum is nonzero. -/
theorem pair_average_attains (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    (v : Fin n → E) (hv : ∀ k, ‖v k‖ = 1) (hmax : |M v| = ‖M‖)
    {i j : Fin n} (hij : i ≠ j) (hplus : v i + v j ≠ 0) :
    |M (pairUpdate v i j (‖v i + v j‖⁻¹ • (v i + v j))
      (‖v i + v j‖⁻¹ • (v i + v j)))| = ‖M‖ := by
  let B : E → E → ℝ := fun x y => M (pairUpdate v i j x y)
  have hcross : B (v i) (v j) = M v := by simp [B, pairUpdate]
  have hcross' : B (v j) (v i) = M v := by
    change M (pairUpdate v i j (v j) (v i)) = _
    rw [pairEval_swap M hM v hij]
    exact hcross
  have hid : B (v i + v j) (v i + v j) - B (v i - v j) (v i - v j) = 4 * M v := by
    dsimp [B]
    simp only [sub_eq_add_neg, ← neg_one_smul ℝ (v j), pairEval_add_left M v hij,
      pairEval_add_right, pairEval_smul_left M v hij, pairEval_smul_right]
    change (B (v i) (v i) + B (v i) (v j) + (B (v j) (v i) + B (v j) (v j))) +
      -(B (v i) (v i) + -1 * B (v i) (v j) +
        (-1 * (B (v j) (v i) + -1 * B (v j) (v j)))) = _
    rw [hcross, hcross']
    ring
  have hpar : ‖v i + v j‖ ^ 2 + ‖v i - v j‖ ^ 2 = 4 := by
    have h := parallelogram_law_with_norm ℝ (v i) (v j)
    rw [hv i, hv j] at h
    norm_num at h ⊢
    exact h
  have hp := pairEval_norm_bound M v hv hij (v i + v j) (v i + v j)
  have hm := pairEval_norm_bound M v hv hij (v i - v j) (v i - v j)
  have ht : 4 * ‖M‖ ≤ |B (v i + v j) (v i + v j)| + |B (v i - v j) (v i - v j)| := by
    calc
      4 * ‖M‖ = |4 * M v| := by rw [abs_mul, hmax]; norm_num
      _ = |B (v i + v j) (v i + v j) - B (v i - v j) (v i - v j)| := congrArg abs hid.symm
      _ ≤ _ := abs_sub _ _
  have heq : |B (v i + v j) (v i + v j)| = ‖M‖ * ‖v i + v j‖ ^ 2 := by
    change |B (v i + v j) (v i + v j)| ≤ _ at hp
    change |B (v i - v j) (v i - v j)| ≤ _ at hm
    have hpar' := congrArg (fun a : ℝ => ‖M‖ * a) hpar
    nlinarith
  change |B (‖v i + v j‖⁻¹ • (v i + v j)) (‖v i + v j‖⁻¹ • (v i + v j))| = _
  dsimp [B]
  rw [pairEval_smul_left M v hij, pairEval_smul_right, abs_mul, abs_mul]
  change |‖v i + v j‖⁻¹| * (|‖v i + v j‖⁻¹| * |B (v i + v j) (v i + v j)|) = _
  rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), heq]
  field_simp [norm_ne_zero_iff.mpr hplus]

end AltOMD.Polarization
