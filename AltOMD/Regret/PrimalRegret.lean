import AltOMD.Regret.BilinearRegret
import AltOMD.Entropy.ConjugateFeasibility

/-!
# Logarithmic regret from the primal mirror minimization updates

A valid primal run supplies feasible minimizers and differentiability at the
relative-interior points where its Bregman objectives are evaluated. The dual
trajectory is constructed here, and its agreement with every primal iterate is
proved. No dual recurrence or primal/dual correspondence is an input.
-/

open scoped ContDiff InnerProductSpace
open Finset

namespace AltOMD.PrimalRegret

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ F := InnerProductSpace.toNormedSpace

/-- A primal mirror run on a finite horizon. Interior and differentiability are
required only at current points, where the paper defines the Bregman divergence;
the last minimizer is required only to be feasible. -/
structure IsMirrorTrajectory (D : Set E) (ψ : E → ℝ) (η : ℝ)
    (loss x : ℕ → E) (T : ℕ) : Prop where
  interior : ∀ k < T, x k ∈ intrinsicInterior ℝ D
  differentiable : ∀ k < T, DifferentiableWithinAt ℝ ψ D (x k)
  next_mem : ∀ k < T, x (k + 1) ∈ D
  minimizes : ∀ k < T, ∀ c ∈ D,
    η * ⟪loss k, x (k + 1)⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D (x k)) (x (k + 1)) (x k) ≤
      η * ⟪loss k, c⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D (x k)) c (x k)

/-- Accumulate dual losses from the initial primal gradient. -/
noncomputable def dualLift (D : Set E) (ψ : E → ℝ) (η : ℝ)
    (loss : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => gradientWithin ψ D x₀
  | k + 1 => dualLift D ψ η loss x₀ k - η • loss k

/-- Every feasible primal minimizer is recovered by the constructed dual run.
This includes the terminal point, without a terminal differentiability premise. -/
theorem gradient_dualLift {D : Set E} {ψ : E → ℝ} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ} (hT : 1 ≤ T)
    (hψ : ConvexOn ℝ D ψ)
    (hfinite : ∀ u, u ∈ Duality.dualDomain D ψ)
    (hdual : Differentiable ℝ (Duality.conjugate D ψ))
    (hrun : IsMirrorTrajectory D ψ η loss x T) :
    ∀ k ≤ T, gradient (Duality.conjugate D ψ) (dualLift D ψ η loss (x 0) k) = x k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      exact InitialDuality.inverse_gradient hψ
        (intrinsicInterior_subset (hrun.interior 0 hT)) (hrun.differentiable 0 hT)
        hfinite (hdual _)
  | succ k ih =>
      intro hk
      have hkT : k < T := hk
      have hback := ih (Nat.le_of_lt hkT)
      change gradient (Duality.conjugate D ψ)
        (dualLift D ψ η loss (x 0) k - η • loss k) = x (k + 1)
      exact PrimalDualStep.mirror_step_gradient_update hψ hfinite (hrun.interior k hkT)
        (hrun.differentiable k hkT) hback (hdual _) (hdual _)
        (hrun.next_mem k hkT) (hrun.minimizes k hkT)

/-- The sum of the two external regrets, expressed directly in primal iterates. -/
noncomputable def sumRegret (DX : Set E) (DY : Set F) (A : E →L[ℝ] F)
    (x : ℕ → E) (y : ℕ → F) (T : ℕ) : ℝ :=
  sSup (Set.range (fun cx : DX => ∑ k ∈ range T,
    (⟪A (x (k + 1)), y k⟫_ℝ - ⟪A cx, y k⟫_ℝ))) +
  sSup (Set.range (fun cy : DY => ∑ k ∈ range T,
    (⟪A (x (k + 1)), cy⟫_ℝ - ⟪A (x (k + 1)), y k⟫_ℝ)))

/-- Passing from recovered primal iterates to the dual regret changes no cost
or supremum. Only the indices appearing in the staggered regret are needed. -/
theorem sumRegret_eq_dual {DX : Set E} {DY : Set F}
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (x u : ℕ → E) (y w : ℕ → F) (T : ℕ)
    (hx : ∀ k ≤ T, gradient (Duality.conjugate DX ψX) (u k) = x k)
    (hy : ∀ k ≤ T, gradient (Duality.conjugate DY ψY) (w k) = y k) :
    sumRegret DX DY A x y T = BilinearRegret.sumRegret DX DY ψX ψY A u w T := by
  have hxcost (cx : DX) :
      (∑ k ∈ range T, (⟪A (x (k + 1)), y k⟫_ℝ - ⟪A cx, y k⟫_ℝ)) =
        ∑ k ∈ range T, BilinearRegret.playerXCosts DX DY ψX ψY A u w cx k := by
    apply sum_congr rfl
    intro k hk
    have hkT := mem_range.mp hk
    simp only [BilinearRegret.playerXCosts, hx (k + 1) hkT,
      hy k (Nat.le_of_lt hkT)]
  have hycost (cy : DY) :
      (∑ k ∈ range T, (⟪A (x (k + 1)), cy⟫_ℝ - ⟪A (x (k + 1)), y k⟫_ℝ)) =
        ∑ k ∈ range T, BilinearRegret.playerYCosts DX DY ψX ψY A u w cy k := by
    apply sum_congr rfl
    intro k hk
    have hkT := mem_range.mp hk
    simp only [BilinearRegret.playerYCosts, hx (k + 1) hkT,
      hy k (Nat.le_of_lt hkT)]
  simp only [sumRegret, BilinearRegret.sumRegret, hxcost, hycost]

/-- The logarithmic regret theorem for the primal AltOMD minimization updates.
The only external algebraic inputs are the same BCH and DSW records as before.
The constructed dual trajectory and its recovery of the given primal iterates
are conclusions of the proof, not hypotheses of this theorem. -/
theorem logarithmic_regret_two_bounds (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hfiniteX : ∀ u, u ∈ Duality.dualDomain DX ψX)
    (hfiniteY : ∀ w, w ∈ Duality.dualDomain DY ψY)
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
    (hxrun : IsMirrorTrajectory DX ψX (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : IsMirrorTrajectory DY ψY (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ∧
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  let η := stepSize (BilinearRegret.gameConstant A K) T
  let u := dualLift DX ψX η (fun k => A.adjoint (y k)) (x 0)
  let w := dualLift DY ψY η (fun k => -A (x (k + 1))) (y 0)
  have hx : ∀ k ≤ T, gradient (Duality.conjugate DX ψX) (u k) = x k :=
    gradient_dualLift hT hψX hfiniteX (hf.differentiable (by simp)) hxrun
  have hy : ∀ k ≤ T, gradient (Duality.conjugate DY ψY) (w k) = y k :=
    gradient_dualLift hT hψY hfiniteY (hg.differentiable (by simp)) hyrun
  rw [sumRegret_eq_dual ψX ψY A x u y w T hx hy]
  apply BilinearRegret.logarithmic_regret_of_primal_initialization_two_bounds
    DX DY ψX ψY A hψX hψY hfiniteX hfiniteY hf hg hK hF hG Z bch dsw T hT
    u w (x 0) (y 0) (hxrun.interior 0 hT) (hyrun.interior 0 hT)
    (hxrun.differentiable 0 hT) (hyrun.differentiable 0 hT) rfl rfl hradius
  · intro k hk
    change u k - η • A.adjoint (y k) = _
    rw [hy k (Nat.le_of_lt hk)]
  · intro k hk
    change w k - η • (-A (x (k + 1))) = _
    rw [hx (k + 1) hk]
    simp only [smul_neg, sub_neg_eq_add, η]

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem logarithmic_regret (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hfiniteX : ∀ u, u ∈ Duality.dualDomain DX ψX)
    (hfiniteY : ∀ w, w ∈ Duality.dualDomain DY ψY)
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
    (hxrun : IsMirrorTrajectory DX ψX (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : IsMirrorTrajectory DY ψY (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  have h := logarithmic_regret_two_bounds DX DY ψX ψY A hψX hψY hfiniteX hfiniteY hf hg hK hF hG Z bch dsw T hT x y hxrun hyrun hradius
  exact h.1.trans h.2

/-- On the paper's compact primal domains, lower semicontinuity supplies the
conjugate-finiteness hypotheses of the primal-run regret theorem. -/
theorem logarithmic_regret_of_compact_two_bounds (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
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
    (hxrun : IsMirrorTrajectory DX ψX (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : IsMirrorTrajectory DY ψY (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ∧
      16 * BilinearRegret.gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  exact logarithmic_regret_two_bounds DX DY ψX ψY A hψX hψY
    (ConjugateFeasibility.conjugate_finite
      ⟨x 0, intrinsicInterior_subset (hxrun.interior 0 hT)⟩ hcompactX hlscX)
    (ConjugateFeasibility.conjugate_finite
      ⟨y 0, intrinsicInterior_subset (hyrun.interior 0 hT)⟩ hcompactY hlscY)
    hf hg hK hF hG Z bch dsw T hT x y hxrun hyrun hradius

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem logarithmic_regret_of_compact (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
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
    (hxrun : IsMirrorTrajectory DX ψX (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => A.adjoint (y k)) x T)
    (hyrun : IsMirrorTrajectory DY ψY (stepSize (BilinearRegret.gameConstant A K) T)
      (fun k => -A (x (k + 1))) y T)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX (x 0)) cx (x 0) +
        Duality.bregman ψY (gradientWithin ψY DY (y 0)) cy (y 0) ≤ Λ) :
    sumRegret DX DY A x y T ≤
      16 * BilinearRegret.gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (BilinearRegret.gameConstant A K) ^ 2 := by
  have h := logarithmic_regret_of_compact_two_bounds DX DY ψX ψY A hcompactX hcompactY hlscX hlscY hψX hψY hf hg hK hF hG Z bch dsw T hT x y hxrun hyrun hradius
  exact h.1.trans h.2

end AltOMD.PrimalRegret
