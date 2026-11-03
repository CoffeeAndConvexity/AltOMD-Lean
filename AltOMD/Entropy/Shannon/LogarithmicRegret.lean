import AltOMD.Entropy.Shannon.Trajectory
import AltOMD.Entropy.ShannonDerivatives
import AltOMD.VerifiedRegret

/-!
# The concrete alternating multiplicative-weights corollary

All regularity, simplex geometry, Legendre, and comparator-radius obligations
are supplied by the Shannon proofs. The public regret theorem assumes only
the game, a positive horizon, strictly positive initial strategies, and the
explicit multiplicative update equations from the manuscript.
-/

open scoped ContDiff InnerProductSpace

namespace AltOMD.Shannon

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

/-- The explicit constant in the entropy corollary, for the Euclidean operator norm. -/
noncomputable def entropyGameConstant
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) : ℝ :=
  384 * max ‖A‖ 1

/-- The actual staggered multiplicative-weights iterates. The second player
uses the first player's newly updated strategy. -/
noncomputable def alternatingWeights
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (η : ℝ)
    (x₀ : EuclideanSpace ℝ ι) (y₀ : EuclideanSpace ℝ κ) :
    ℕ → EuclideanSpace ℝ ι × EuclideanSpace ℝ κ
  | 0 => (x₀, y₀)
  | k + 1 =>
    let z := alternatingWeights A η x₀ y₀ k
    let x := multiplicativeWeights z.1 (A.adjoint z.2) η
    (x, multiplicativeWeights z.2 (-A x) η)

@[simp] theorem alternatingWeights_zero
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (η : ℝ)
    (x₀ : EuclideanSpace ℝ ι) (y₀ : EuclideanSpace ℝ κ) :
    alternatingWeights A η x₀ y₀ 0 = (x₀, y₀) := rfl

theorem alternatingWeights_step_left
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (η : ℝ)
    (x₀ : EuclideanSpace ℝ ι) (y₀ : EuclideanSpace ℝ κ) (k : ℕ) :
    (alternatingWeights A η x₀ y₀ (k + 1)).1 =
      multiplicativeWeights (alternatingWeights A η x₀ y₀ k).1
        (A.adjoint (alternatingWeights A η x₀ y₀ k).2) η := rfl

theorem alternatingWeights_step_right
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (η : ℝ)
    (x₀ : EuclideanSpace ℝ ι) (y₀ : EuclideanSpace ℝ κ) (k : ℕ) :
    (alternatingWeights A η x₀ y₀ (k + 1)).2 =
      multiplicativeWeights (alternatingWeights A η x₀ y₀ k).2
        (-A (alternatingWeights A η x₀ y₀ (k + 1)).1) η := rfl

theorem gameConstant_four
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) :
    BilinearRegret.gameConstant A 4 = entropyGameConstant A := by
  unfold BilinearRegret.gameConstant entropyGameConstant
  ring

/-- The actual Shannon conjugate has the factorial bound with the improved `K = 4`. -/
theorem norm_iteratedFDeriv_conjugate_le (r : ℕ) (u : EuclideanSpace ℝ ι)
    (hr : 1 ≤ r) :
    ‖iteratedFDeriv ℝ r (Duality.conjugate simplex entropy) u‖ ≤
      (4 : ℝ) ^ r * r.factorial := by
  rw [conjugate_eq_logSumExp]
  apply (norm_iteratedFDeriv_logSumExp_le_sharp r u hr).trans
  have hp : (2 : ℝ) ^ (r - 1) ≤ (4 : ℝ) ^ r :=
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) r)
  exact mul_le_mul_of_nonneg_right hp (by positivity)

/-- Both global derivative suprema obey the manuscript's combined regularity assumption. -/
theorem sum_sup_derivatives_le (r : ℕ) (hr : 1 ≤ r) :
    (⨆ u : EuclideanSpace ℝ ι, ‖iteratedFDeriv ℝ r logSumExp u‖) +
      (⨆ w : EuclideanSpace ℝ κ, ‖iteratedFDeriv ℝ r logSumExp w‖) ≤
        (4 : ℝ) ^ r * r.factorial := by
  have hx : (⨆ u : EuclideanSpace ℝ ι, ‖iteratedFDeriv ℝ r logSumExp u‖) ≤
      (2 : ℝ) ^ (r - 1) * r.factorial :=
    ciSup_le (fun u => norm_iteratedFDeriv_logSumExp_le_sharp r u hr)
  have hy : (⨆ w : EuclideanSpace ℝ κ, ‖iteratedFDeriv ℝ r logSumExp w‖) ≤
      (2 : ℝ) ^ (r - 1) * r.factorial :=
    ciSup_le (fun w => norm_iteratedFDeriv_logSumExp_le_sharp r w hr)
  have hpow : (2 : ℝ) * 2 ^ (r - 1) = 2 ^ r := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  calc
    _ ≤ 2 * ((2 : ℝ) ^ (r - 1) * r.factorial) := by linarith
    _ = (2 : ℝ) ^ r * r.factorial := by rw [← mul_assoc, hpow]
    _ ≤ (4 : ℝ) ^ r * r.factorial := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num) (by norm_num) r) (by positivity)

/-- Corollary `cor:entropy`: alternating multiplicative weights with strictly
positive initial strategies has the explicit logarithmic regret bound. -/
theorem logarithmic_regret
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (T : ℕ) (hT : 1 ≤ T)
    (x : ℕ → EuclideanSpace ℝ ι) (y : ℕ → EuclideanSpace ℝ κ)
    (hx0 : x 0 ∈ simplex) (hy0 : y 0 ∈ simplex)
    (hxpos : ∀ i, 0 < x 0 i) (hypos : ∀ j, 0 < y 0 j)
    (hxstep : ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (A.adjoint (y k))
      (stepSize (entropyGameConstant A) T))
    (hystep : ∀ k < T, y (k + 1) = multiplicativeWeights (y k) (-A (x (k + 1)))
      (stepSize (entropyGameConstant A) T)) :
    PrimalRegret.sumRegret simplex simplex A x y T ≤
      16 * entropyGameConstant A *
        (Real.log (1 / minCoordinate (x 0)) + Real.log (1 / minCoordinate (y 0))) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  have hrunX := multiplicativeWeights_isPrimalMirrorTrajectory hx0 hxpos hxstep
  have hrunY := multiplicativeWeights_isPrimalMirrorTrajectory hy0 hypos hystep
  have hf : ContDiff ℝ ∞ (Duality.conjugate simplex (entropy : EuclideanSpace ℝ ι → ℝ)) := by
    rw [conjugate_eq_logSumExp]
    exact contDiff_logSumExp
  have hg : ContDiff ℝ ∞ (Duality.conjugate simplex (entropy : EuclideanSpace ℝ κ → ℝ)) := by
    rw [conjugate_eq_logSumExp]
    exact contDiff_logSumExp
  have hbound := VerifiedRegret.logarithmic_regret simplex simplex entropy entropy A
    isCompact_simplex isCompact_simplex
    (continuous_entropy.lowerSemicontinuous.lowerSemicontinuousOn simplex)
    (continuous_entropy.lowerSemicontinuous.lowerSemicontinuousOn simplex)
    convexOn_entropy convexOn_entropy
    (fun _ hx => differentiableWithinAt_entropy hx)
    (fun _ hy => differentiableWithinAt_entropy hy)
    gradientBlowsUpAtBoundary_entropy gradientBlowsUpAtBoundary_entropy hf hg
    (K := 4) (by norm_num)
    norm_iteratedFDeriv_conjugate_le norm_iteratedFDeriv_conjugate_le T hT x y
    (by simpa only [gameConstant_four] using hrunX)
    (by simpa only [gameConstant_four] using hrunY)
    (fun cx hcx cy hcy => add_le_add
      (bregman_le_radius hcx hx0 hxpos) (bregman_le_radius hcy hy0 hypos))
  simpa only [gameConstant_four] using hbound

/-- The general entropy corollary for the recursively defined algorithm. -/
theorem alternatingWeights_regret
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (T : ℕ) (hT : 1 ≤ T)
    (x₀ : EuclideanSpace ℝ ι) (y₀ : EuclideanSpace ℝ κ)
    (hx₀ : x₀ ∈ simplex) (hy₀ : y₀ ∈ simplex)
    (hxpos : ∀ i, 0 < x₀ i) (hypos : ∀ j, 0 < y₀ j) :
    let z := alternatingWeights A (stepSize (entropyGameConstant A) T) x₀ y₀
    PrimalRegret.sumRegret simplex simplex A (fun k => (z k).1) (fun k => (z k).2) T ≤
      16 * entropyGameConstant A *
        (Real.log (1 / minCoordinate x₀) + Real.log (1 / minCoordinate y₀)) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  dsimp only
  apply logarithmic_regret A T hT _ _ hx₀ hy₀ hxpos hypos
  · intro k _
    exact alternatingWeights_step_left A _ x₀ y₀ k
  · intro k _
    exact alternatingWeights_step_right A _ x₀ y₀ k

/-- Equation `eq:entropy-regret`: the uniform-initialization specialization. -/
theorem logarithmic_regret_uniform
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (T : ℕ) (hT : 1 ≤ T)
    (x : ℕ → EuclideanSpace ℝ ι) (y : ℕ → EuclideanSpace ℝ κ)
    (hx0 : x 0 = uniform) (hy0 : y 0 = uniform)
    (hxstep : ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (A.adjoint (y k))
      (stepSize (entropyGameConstant A) T))
    (hystep : ∀ k < T, y (k + 1) = multiplicativeWeights (y k) (-A (x (k + 1)))
      (stepSize (entropyGameConstant A) T)) :
    PrimalRegret.sumRegret simplex simplex A x y T ≤
      16 * entropyGameConstant A * Real.log ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  have h := logarithmic_regret A T hT x y
    (hx0.symm ▸ uniform_mem_simplex) (hy0.symm ▸ uniform_mem_simplex)
    (by simpa only [hx0] using (uniform_pos (ι := ι)))
    (by simpa only [hy0] using (uniform_pos (ι := κ))) hxstep hystep
  simpa only [hx0, hy0, uniform_pair_radius] using h

/-- The uniform-initialization corollary for the recursively defined algorithm;
there are no trajectory or analytic obligations left as hypotheses. -/
theorem alternatingWeights_regret_uniform
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (T : ℕ) (hT : 1 ≤ T) :
    let z := alternatingWeights A (stepSize (entropyGameConstant A) T) uniform uniform
    PrimalRegret.sumRegret simplex simplex A (fun k => (z k).1) (fun k => (z k).2) T ≤
      16 * entropyGameConstant A * Real.log ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  dsimp only
  apply logarithmic_regret_uniform A T hT _ _ rfl rfl
  · intro k _
    exact alternatingWeights_step_left A _ uniform uniform k
  · intro k _
    exact alternatingWeights_step_right A _ uniform uniform k

end AltOMD.Shannon
