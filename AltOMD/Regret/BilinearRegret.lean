import AltOMD.Regret.Main
import AltOMD.Hamiltonian.BilinearSystem
import AltOMD.Regret.Comparator
import AltOMD.Entropy.InitialDuality
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Logarithmic regret for the dual formulation of alternating mirror descent

The only external algebraic hypotheses are universal BCH and DSW. Comparator
identities, the initial Bregman conversion, terminal coupling nonnegativity,
and both modified-energy estimates are derived in the imported proofs.
-/

open scoped ContDiff InnerProductSpace
open scoped Pointwise
open Finset

namespace AltOMD.BilinearRegret

/-- A bounded joint family of separated costs has the sum of the two individual
suprema as its supremum. Boundedness of each family is derived from the joint one. -/
theorem supremum_separated {X Y : Type*} [Nonempty X] [Nonempty Y]
    (a : X → ℝ) (b : Y → ℝ)
    (hbound : BddAbove (Set.range (fun p : X × Y => a p.1 + b p.2))) :
    sSup (Set.range (fun p : X × Y => a p.1 + b p.2)) =
      sSup (Set.range a) + sSup (Set.range b) := by
  classical
  obtain ⟨U, hU⟩ := hbound
  let x₀ : X := Classical.choice inferInstance
  let y₀ : Y := Classical.choice inferInstance
  have ha : BddAbove (Set.range a) := by
    refine ⟨U - b y₀, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h := hU ⟨(x, y₀), rfl⟩
    linarith
  have hb : BddAbove (Set.range b) := by
    refine ⟨U - a x₀, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hU ⟨(x₀, y), rfl⟩
    linarith
  have hrange : Set.range (fun p : X × Y => a p.1 + b p.2) =
      Set.range a + Set.range b := by
    ext t
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact Set.add_mem_add ⟨x, rfl⟩ ⟨y, rfl⟩
    · rintro ⟨v, ⟨x, rfl⟩, w, ⟨y, rfl⟩, rfl⟩
      exact ⟨(x, y), rfl⟩
  rw [hrange]
  exact csSup_add (Set.range_nonempty _) ha (Set.range_nonempty _) hb

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ F := InnerProductSpace.toNormedSpace

noncomputable def gameConstant (A : E →L[ℝ] F) (K : ℝ) : ℝ :=
  24 * max ‖A‖ 1 * K ^ 2

noncomputable def costs (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (u : ℕ → E) (w : ℕ → F) (c : DX × DY) (k : ℕ) : ℝ :=
  Comparator.cost A c.1 c.2
    (gradient (Duality.conjugate DX ψX) (u (k + 1)))
    (gradient (Duality.conjugate DY ψY) (w k))

noncomputable def playerXCosts (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (u : ℕ → E) (w : ℕ → F) (cx : DX) (k : ℕ) : ℝ :=
  ⟪A (gradient (Duality.conjugate DX ψX) (u (k + 1))),
      gradient (Duality.conjugate DY ψY) (w k)⟫_ℝ -
    ⟪A cx, gradient (Duality.conjugate DY ψY) (w k)⟫_ℝ

noncomputable def playerYCosts (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (u : ℕ → E) (w : ℕ → F) (cy : DY) (k : ℕ) : ℝ :=
  ⟪A (gradient (Duality.conjugate DX ψX) (u (k + 1))), cy⟫_ℝ -
    ⟪A (gradient (Duality.conjugate DX ψX) (u (k + 1))),
      gradient (Duality.conjugate DY ψY) (w k)⟫_ℝ

/-- The sum of the two players' separate external regrets. -/
noncomputable def sumRegret (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (u : ℕ → E) (w : ℕ → F) (T : ℕ) : ℝ :=
  sSup (Set.range (fun cx : DX => ∑ k ∈ range T, playerXCosts DX DY ψX ψY A u w cx k)) +
    sSup (Set.range (fun cy : DY => ∑ k ∈ range T, playerYCosts DX DY ψX ψY A u w cy k))

theorem sumRegret_eq_totalRegret (DX : Set E) (DY : Set F) [Nonempty DX] [Nonempty DY]
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (u : ℕ → E) (w : ℕ → F) (T : ℕ)
    (hbound : BddAbove (Set.range (fun c : DX × DY =>
      ∑ k ∈ range T, costs DX DY ψX ψY A u w c k))) :
    sumRegret DX DY ψX ψY A u w T = totalRegret (costs DX DY ψX ψY A u w) T := by
  have hsplit (c : DX × DY) :
      (∑ k ∈ range T, playerXCosts DX DY ψX ψY A u w c.1 k) +
          (∑ k ∈ range T, playerYCosts DX DY ψX ψY A u w c.2 k) =
        ∑ k ∈ range T, costs DX DY ψX ψY A u w c k := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    simp only [playerXCosts, playerYCosts, costs, Comparator.cost]
    ring
  have hrange : Set.range (fun c : DX × DY =>
      (∑ k ∈ range T, playerXCosts DX DY ψX ψY A u w c.1 k) +
        (∑ k ∈ range T, playerYCosts DX DY ψX ψY A u w c.2 k)) =
      Set.range (fun c : DX × DY => ∑ k ∈ range T, costs DX DY ψX ψY A u w c k) := by
    congr 1
    funext c
    exact hsplit c
  have heq := supremum_separated
    (fun cx : DX => ∑ k ∈ range T, playerXCosts DX DY ψX ψY A u w cx k)
    (fun cy : DY => ∑ k ∈ range T, playerYCosts DX DY ψX ψY A u w cy k)
    (hrange.symm ▸ hbound)
  rw [hrange] at heq
  exact heq.symm

/-- AltOMD's logarithmic regret bound from convex duality, factorial derivative
bounds, and the actual alternating updates. No energy or comparator estimate is
an assumption of this theorem. -/
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
    (T : ℕ) (hT : 1 ≤ T) (u : ℕ → E) (w : ℕ → F)
    (hx0 : gradient (Duality.conjugate DX ψX) (u 0) ∈ intrinsicInterior ℝ DX)
    (hy0 : gradient (Duality.conjugate DY ψY) (w 0) ∈ intrinsicInterior ℝ DY)
    (hψXdiff : DifferentiableWithinAt ℝ ψX DX
      (gradient (Duality.conjugate DX ψX) (u 0)))
    (hψYdiff : DifferentiableWithinAt ℝ ψY DY
      (gradient (Duality.conjugate DY ψY) (w 0)))
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX
          (gradientWithin ψX DX (gradient (Duality.conjugate DX ψX) (u 0)))
          cx (gradient (Duality.conjugate DX ψX) (u 0)) +
        Duality.bregman ψY
          (gradientWithin ψY DY (gradient (Duality.conjugate DY ψY) (w 0)))
          cy (gradient (Duality.conjugate DY ψY) (w 0)) ≤ Λ)
    (hu : ∀ k < T, u (k + 1) = u k - stepSize (gameConstant A K) T •
      A.adjoint (gradient (Duality.conjugate DY ψY) (w k)))
    (hw : ∀ k < T, w (k + 1) = w k + stepSize (gameConstant A K) T •
      A (gradient (Duality.conjugate DX ψX) (u (k + 1)))) :
    sumRegret DX DY ψX ψY A u w T ≤
      16 * gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 ∧
      16 * gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 ≤
      16 * gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 := by
  have _horizon_positive : 0 < T := hT
  let f := Duality.conjugate DX ψX
  let g := Duality.conjugate DY ψY
  let S := BilinearSystem.system A f g hf hg
  let z : ℕ → E × F := fun k => (u k, w k)
  let Γ : DX × DY → ℕ → ℝ := fun c k =>
    Comparator.coupling DX DY ψX ψY c.1 c.2 (u k) (w k)
  let : Nonempty DX := ⟨⟨gradient f (u 0), intrinsicInterior_subset hx0⟩⟩
  let : Nonempty DY := ⟨⟨gradient g (w 0), intrinsicInterior_subset hy0⟩⟩
  have hC : 0 < gameConstant A K := by
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    unfold gameConstant
    positivity
  have hΛ : 0 ≤ Λ := by
    have hb := hradius (gradient f (u 0)) (intrinsicInterior_subset hx0)
      (gradient g (w 0)) (intrinsicInterior_subset hy0)
    simpa only [f, g, Duality.bregman, sub_self, inner_zero_right, add_zero] using hb
  have hinitial (c : DX × DY) : Γ c 0 ≤ Λ := by
    dsimp only [Γ]
    rw [Comparator.coupling_eq_bregman hψX hψY hx0 hy0
      hψXdiff.hasGradientWithinAt.hasFDerivWithinAt
      hψYdiff.hasGradientWithinAt.hasFDerivWithinAt
      (hfiniteX (u 0)) (hfiniteY (w 0))
      ((hf.differentiable (by simp) (u 0)).hasGradientAt.hasFDerivAt)
      ((hg.differentiable (by simp) (w 0)).hasGradientAt.hasFDerivAt)
      c.1.property c.2.property]
    exact hradius c.1 c.1.property c.2 c.2.property
  have htrajectory : ∀ k < T,
      z (k + 1) = S.step (stepSize (gameConstant A K) T) (z k) := by
    intro k hk
    dsimp only [z, S]
    rw [BilinearSystem.system_step]
    apply Prod.ext
    · exact hu k hk
    · change w (k + 1) = w k + stepSize (gameConstant A K) T •
        A (gradient f (u k - stepSize (gameConstant A K) T • A.adjoint (gradient g (w k))))
      rw [← hu k hk]
      exact hw k hk
  have hbounded : BddAbove (Set.range (fun c : DX × DY =>
      ∑ k ∈ range T, costs DX DY ψX ψY A u w c k)) := by
    refine ⟨(Comparator.energy DX DY ψX ψY (u T) (w T) -
      Comparator.energy DX DY ψX ψY (u 0) (w 0) + Λ) / stepSize (gameConstant A K) T, ?_⟩
    rintro _ ⟨c, rfl⟩
    apply (le_div_iff₀ (stepSize_pos hC T)).2
    have hi := Comparator.trajectory_identity DX DY ψX ψY A c.1 c.2
      u w (stepSize (gameConstant A K) T) T hu hw
    have hs := hinitial c
    have he := Comparator.coupling_nonneg c.1.property c.2.property
      (hfiniteX (u T)) (hfiniteY (w T))
    dsimp only [costs, Γ] at hs ⊢
    nlinarith
  rw [sumRegret_eq_totalRegret DX DY ψX ψY A u w T hbounded]
  apply AltOMD.logarithmic_regret_two_bounds S hK hC hΛ
    (BilinearSystem.bracketConstant_le A K)
    (BilinearSystem.second_regularity g hg K hG)
    (BilinearSystem.first_regularity f hf K hF)
    Z bch dsw T z (costs DX DY ψX ψY A u w) Γ htrajectory
  · intro c k hk
    exact Comparator.altomd_one_step_identity DX DY ψX ψY A c.1 c.2
      (u k) (u (k + 1)) (w k) (w (k + 1)) (stepSize (gameConstant A K) T)
      (hu k hk) (hw k hk)
  · intro c
    exact Comparator.coupling_nonneg c.1.property c.2.property
      (hfiniteX (u T)) (hfiniteY (w T))
  · exact hinitial

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
    (T : ℕ) (hT : 1 ≤ T) (u : ℕ → E) (w : ℕ → F)
    (hx0 : gradient (Duality.conjugate DX ψX) (u 0) ∈ intrinsicInterior ℝ DX)
    (hy0 : gradient (Duality.conjugate DY ψY) (w 0) ∈ intrinsicInterior ℝ DY)
    (hψXdiff : DifferentiableWithinAt ℝ ψX DX
      (gradient (Duality.conjugate DX ψX) (u 0)))
    (hψYdiff : DifferentiableWithinAt ℝ ψY DY
      (gradient (Duality.conjugate DY ψY) (w 0)))
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX
          (gradientWithin ψX DX (gradient (Duality.conjugate DX ψX) (u 0)))
          cx (gradient (Duality.conjugate DX ψX) (u 0)) +
        Duality.bregman ψY
          (gradientWithin ψY DY (gradient (Duality.conjugate DY ψY) (w 0)))
          cy (gradient (Duality.conjugate DY ψY) (w 0)) ≤ Λ)
    (hu : ∀ k < T, u (k + 1) = u k - stepSize (gameConstant A K) T •
      A.adjoint (gradient (Duality.conjugate DY ψY) (w k)))
    (hw : ∀ k < T, w (k + 1) = w k + stepSize (gameConstant A K) T •
      A (gradient (Duality.conjugate DX ψX) (u (k + 1)))) :
    sumRegret DX DY ψX ψY A u w T ≤
      16 * gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 := by
  have h := logarithmic_regret_two_bounds DX DY ψX ψY A hψX hψY hfiniteX hfiniteY hf hg hK hF hG Z bch dsw T hT u w hx0 hy0 hψXdiff hψYdiff hradius hu hw
  exact h.1.trans h.2

/-- The manuscript initialization by primal relative gradients. The inverse
gradient identities needed to invoke the preceding theorem are proved from
convexity and differentiability in `InitialDuality`. -/
theorem logarithmic_regret_of_primal_initialization_two_bounds (DX : Set E) (DY : Set F)
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
    (T : ℕ) (hT : 1 ≤ T) (u : ℕ → E) (w : ℕ → F)
    (x0 : E) (y0 : F)
    (hx0 : x0 ∈ intrinsicInterior ℝ DX) (hy0 : y0 ∈ intrinsicInterior ℝ DY)
    (hψXdiff : DifferentiableWithinAt ℝ ψX DX x0)
    (hψYdiff : DifferentiableWithinAt ℝ ψY DY y0)
    (hu0 : u 0 = gradientWithin ψX DX x0) (hw0 : w 0 = gradientWithin ψY DY y0)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX x0) cx x0 +
        Duality.bregman ψY (gradientWithin ψY DY y0) cy y0 ≤ Λ)
    (hu : ∀ k < T, u (k + 1) = u k - stepSize (gameConstant A K) T •
      A.adjoint (gradient (Duality.conjugate DY ψY) (w k)))
    (hw : ∀ k < T, w (k + 1) = w k + stepSize (gameConstant A K) T •
      A (gradient (Duality.conjugate DX ψX) (u (k + 1)))) :
    sumRegret DX DY ψX ψY A u w T ≤
      16 * gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 ∧
      16 * gameConstant A K * Λ * ((Nat.log 2 T : ℝ) + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 ≤
      16 * gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 := by
  have hxback : gradient (Duality.conjugate DX ψX) (u 0) = x0 := by
    rw [hu0]
    exact InitialDuality.inverse_gradient hψX (intrinsicInterior_subset hx0) hψXdiff
      hfiniteX (hf.differentiable (by simp) _)
  have hyback : gradient (Duality.conjugate DY ψY) (w 0) = y0 := by
    rw [hw0]
    exact InitialDuality.inverse_gradient hψY (intrinsicInterior_subset hy0) hψYdiff
      hfiniteY (hg.differentiable (by simp) _)
  refine logarithmic_regret_two_bounds DX DY ψX ψY A hψX hψY hfiniteX hfiniteY hf hg
    hK hF hG Z bch dsw T hT u w ?_ ?_ ?_ ?_ ?_ hu hw
  · simpa only [hxback] using hx0
  · simpa only [hyback] using hy0
  · simpa only [hxback] using hψXdiff
  · simpa only [hyback] using hψYdiff
  · simpa only [hxback, hyback] using hradius

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem logarithmic_regret_of_primal_initialization (DX : Set E) (DY : Set F)
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
    (T : ℕ) (hT : 1 ≤ T) (u : ℕ → E) (w : ℕ → F)
    (x0 : E) (y0 : F)
    (hx0 : x0 ∈ intrinsicInterior ℝ DX) (hy0 : y0 ∈ intrinsicInterior ℝ DY)
    (hψXdiff : DifferentiableWithinAt ℝ ψX DX x0)
    (hψYdiff : DifferentiableWithinAt ℝ ψY DY y0)
    (hu0 : u 0 = gradientWithin ψX DX x0) (hw0 : w 0 = gradientWithin ψY DY y0)
    (hradius : ∀ cx ∈ DX, ∀ cy ∈ DY,
      Duality.bregman ψX (gradientWithin ψX DX x0) cx x0 +
        Duality.bregman ψY (gradientWithin ψY DY y0) cy y0 ≤ Λ)
    (hu : ∀ k < T, u (k + 1) = u k - stepSize (gameConstant A K) T •
      A.adjoint (gradient (Duality.conjugate DY ψY) (w k)))
    (hw : ∀ k < T, w (k + 1) = w k + stepSize (gameConstant A K) T •
      A (gradient (Duality.conjugate DX ψX) (u (k + 1)))) :
    sumRegret DX DY ψX ψY A u w T ≤
      16 * gameConstant A K * Λ * (Real.logb 2 T + 2) +
        ((128 / 3 : ℝ) + 4 * Real.exp 2) * (gameConstant A K) ^ 2 := by
  have h := logarithmic_regret_of_primal_initialization_two_bounds DX DY ψX ψY A hψX hψY hfiniteX hfiniteY hf hg hK hF hG Z bch dsw T hT u w x0 y0 hx0 hy0 hψXdiff hψYdiff hu0 hw0 hradius hu hw
  exact h.1.trans h.2

end AltOMD.BilinearRegret
