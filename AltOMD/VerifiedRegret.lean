import AltOMD.Regret.LegendreRegret
import AltOMD.Hamiltonian.BCHTheorem

/-!
# Logarithmic regret with proved BCH coefficients

This specialization applies the proved BCH exponential identity and explicit
Hamiltonian representation directly to the canonical Lie expressions.
Its premises consist solely of the
analytic, geometric, initialization, and primal-update assumptions.
-/

open scoped ContDiff InnerProductSpace

namespace AltOMD.VerifiedRegret

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The primal Legendre regret bound, with the classical algebraic identities
supplied by kernel-checked proofs for a single canonical coefficient sequence. -/
theorem logarithmic_regret_two_bounds (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z)
    (hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (hf : ContDiff ℝ ∞ (Duality.conjugate DX ψX))
    (hg : ContDiff ℝ ∞ (Duality.conjugate DY ψY))
    {K Λ : ℝ} (hK : 1 ≤ K)
    (hF : ∀ r u, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DX ψX) u‖ ≤ K ^ r * r.factorial)
    (hG : ∀ r w, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DY ψY) w‖ ≤ K ^ r * r.factorial)
    (T : ℕ) (hT : 1 ≤ T) (x : ℕ → E) (y : ℕ → F)
    (hxrun : LegendreTrajectory.IsPrimalMirrorTrajectory DX ψX
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : LegendreTrajectory.IsPrimalMirrorTrajectory DY ψY
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    PrimalRegret.sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ∧
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  exact LegendreRegret.logarithmic_regret_two_bounds DX DY ψX ψY A
    hcompactX hcompactY hlscX hlscY hψX hψY hdiffX hdiffY hsteepX hsteepY
    hf hg hK hF hG BCHCoefficients.coefficient BCHTheorem.classicalBCHInput
    BCHCoefficients.classicalDSWInput T hT x y hxrun hyrun hradius

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem logarithmic_regret (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z)
    (hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (hf : ContDiff ℝ ∞ (Duality.conjugate DX ψX))
    (hg : ContDiff ℝ ∞ (Duality.conjugate DY ψY))
    {K Λ : ℝ} (hK : 1 ≤ K)
    (hF : ∀ r u, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DX ψX) u‖ ≤ K ^ r * r.factorial)
    (hG : ∀ r w, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DY ψY) w‖ ≤ K ^ r * r.factorial)
    (T : ℕ) (hT : 1 ≤ T) (x : ℕ → E) (y : ℕ → F)
    (hxrun : LegendreTrajectory.IsPrimalMirrorTrajectory DX ψX
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : LegendreTrajectory.IsPrimalMirrorTrajectory DY ψY
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    PrimalRegret.sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  have h := logarithmic_regret_two_bounds DX DY ψX ψY A hcompactX hcompactY hlscX hlscY hψX hψY hdiffX hdiffY hsteepX hsteepY hf hg hK hF hG T hT x y hxrun hyrun hradius
  exact h.1.trans h.2

/-- The two inequalities of the main theorem, with the initial radius defined
by its two comparator suprema and the summed derivative assumption retained.
The regularizers are represented by their real restrictions to the compact
strategy sets; finite comparator radius excludes infinite values on those sets.
Relative continuous differentiability is stated in affine-hull coordinates. -/
theorem logarithmic_regret_source (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hstrictX : StrictConvexOn ℝ (intrinsicInterior ℝ DX) ψX)
    (hstrictY : StrictConvexOn ℝ (intrinsicInterior ℝ DY) ψY)
    (hc1X : ∀ z ∈ intrinsicInterior ℝ DX,
      ContDiffAt ℝ 1 (fun v : (affineSpan ℝ DX).direction => ψX (z + (v : E))) 0)
    (hc1Y : ∀ z ∈ intrinsicInterior ℝ DY,
      ContDiffAt ℝ 1 (fun v : (affineSpan ℝ DY).direction => ψY (z + (v : F))) 0)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (hf : ContDiff ℝ ∞ (Duality.conjugate DX ψX))
    (hg : ContDiff ℝ ∞ (Duality.conjugate DY ψY))
    {K : ℝ} (hK : 1 ≤ K)
    (hderivative : ∀ r, 1 ≤ r → ∀ u w,
      ‖iteratedFDeriv ℝ r (Duality.conjugate DX ψX) u‖ +
        ‖iteratedFDeriv ℝ r (Duality.conjugate DY ψY) w‖ ≤ K ^ r * r.factorial)
    (x₀ : E) (y₀ : F)
    (hx₀ : x₀ ∈ intrinsicInterior ℝ DX) (hy₀ : y₀ ∈ intrinsicInterior ℝ DY)
    (hradiusX : BddAbove ((fun c =>
      Duality.bregman ψX (gradientWithin ψX DX x₀) c x₀) '' DX))
    (hradiusY : BddAbove ((fun c =>
      Duality.bregman ψY (gradientWithin ψY DY y₀) c y₀) '' DY))
    (T : ℕ) (hT : 1 ≤ T) (x : ℕ → E) (y : ℕ → F)
    (hxinitial : x 0 = x₀) (hyinitial : y 0 = y₀)
    (hxrun : LegendreTrajectory.IsPrimalMirrorTrajectory DX ψX
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : LegendreTrajectory.IsPrimalMirrorTrajectory DY ψY
      (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T) :
    let Λ₀ := sSup ((fun c =>
        Duality.bregman ψX (gradientWithin ψX DX x₀) c x₀) '' DX) +
      sSup ((fun c =>
        Duality.bregman ψY (gradientWithin ψY DY y₀) c y₀) '' DY)
    let C₀ := BilinearRegret.gameConstant A K
    PrimalRegret.sumRegret DX DY A x y T ≤
        16 * C₀ * Λ₀ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ∧
      16 * C₀ * Λ₀ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ≤
        16 * C₀ * Λ₀ * (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
  have hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z := by
    intro z hz
    exact differentiableWithinAt_of_affineChart (intrinsicInterior_subset hz)
      ((hc1X z hz).differentiableAt (by norm_num))
  have hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z := by
    intro z hz
    exact differentiableWithinAt_of_affineChart (intrinsicInterior_subset hz)
      ((hc1Y z hz).differentiableAt (by norm_num))
  have hF : ∀ r u, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DX ψX) u‖ ≤ K ^ r * r.factorial := by
    intro r u hr
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hderivative r hr u 0)
  have hG : ∀ r w, 1 ≤ r →
      ‖iteratedFDeriv ℝ r (Duality.conjugate DY ψY) w‖ ≤ K ^ r * r.factorial := by
    intro r w hr
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hderivative r hr 0 w)
  dsimp only
  apply logarithmic_regret_two_bounds DX DY ψX ψY A hcompactX hcompactY
    hlscX hlscY hψX hψY hdiffX hdiffY hsteepX hsteepY hf hg hK hF hG
    T hT x y hxrun hyrun
  intro cx hcx cy hcy
  rw [hxinitial, hyinitial]
  exact add_le_add (le_csSup hradiusX ⟨cx, hcx, rfl⟩)
    (le_csSup hradiusY ⟨cy, hcy, rfl⟩)

end AltOMD.VerifiedRegret
