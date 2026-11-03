import AltOMD.Regret.LegendreTrajectory

/-!
# Logarithmic regret for primal Legendre mirror updates

Interior preservation is proved from relative gradient blowup and optimality.
The algorithmic hypotheses specify an interior starting point and feasible
primal minimizers; they no longer assume interiority or differentiability of
the later iterates. The two classical algebraic inputs remain explicit.
-/

open scoped ContDiff InnerProductSpace

namespace AltOMD.LegendreRegret

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The paper's primal regret bound with iterate interiority derived from the
Legendre assumptions. The existence theorem in `LegendreTrajectory` constructs
runs satisfying precisely the two primal trajectory premises below. -/
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
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar (E × F)))
    (dsw : WordCoefficients.ClassicalDSWInput Z (SmoothScalar (E × F)))
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
  exact PrimalRegret.logarithmic_regret_of_compact_two_bounds DX DY ψX ψY A
    hcompactX hcompactY hlscX hlscY hψX hψY hf hg hK hF hG Z bch dsw T hT x y
    (hxrun.toIsMirrorTrajectory hψX hdiffX hsteepX)
    (hyrun.toIsMirrorTrajectory hψY hdiffY hsteepY) hradius

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
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar (E × F)))
    (dsw : WordCoefficients.ClassicalDSWInput Z (SmoothScalar (E × F)))
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
  have h := logarithmic_regret_two_bounds DX DY ψX ψY A hcompactX hcompactY hlscX hlscY hψX hψY hdiffX hdiffY hsteepX hsteepY hf hg hK hF hG Z bch dsw T hT x y hxrun hyrun hradius
  exact h.1.trans h.2

end AltOMD.LegendreRegret
