import AltOMD.Entropy.Duality

/-!
# Primal initialization through conjugate gradients

The conjugate gradient inverts the actual relative primal gradient at a
differentiability point. This follows from a supporting hyperplane and Fermat's
theorem; no inverse-gradient or Fenchel equality is an external hypothesis.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD.InitialDuality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The supporting functional at a primal point attains the defining supremum
of the conjugate, even when the primal domain has empty ambient interior. -/
theorem conjugate_at_primal_gradient {D : Set E} {ψ : E → ℝ} {x : E}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ D)
    (hdiff : DifferentiableWithinAt ℝ ψ D x) :
    Duality.conjugate D ψ (gradientWithin ψ D x) =
      ⟪gradientWithin ψ D x, x⟫_ℝ - ψ x := by
  have hs (y : E) (hy : y ∈ D) :
      ⟪gradientWithin ψ D x, y⟫_ℝ - ψ y ≤
        ⟪gradientWithin ψ D x, x⟫_ℝ - ψ x := by
    have h := Duality.supporting_inequality hψ hx hy
      hdiff.hasGradientWithinAt.hasFDerivWithinAt
    simp only [InnerProductSpace.toDual_apply_apply, inner_sub_right] at h
    linarith
  have hg : gradientWithin ψ D x ∈ Duality.dualDomain D ψ := by
    refine ⟨⟪gradientWithin ψ D x, x⟫_ℝ - ψ x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hs y hy
  exact le_antisymm (Duality.conjugate_le ⟨x, hx⟩ hs) (Duality.le_conjugate hg hx)

/-- The inverse-gradient identity used to initialize the dual trajectory from
a supplied primal point. Every derivative in the statement is an actual derivative. -/
theorem inverse_gradient {D : Set E} {ψ : E → ℝ} {x : E}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ D)
    (hdiff : DifferentiableWithinAt ℝ ψ D x)
    (hfinite : ∀ u, u ∈ Duality.dualDomain D ψ)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (gradientWithin ψ D x)) :
    gradient (Duality.conjugate D ψ) (gradientWithin ψ D x) = x := by
  have hattain := conjugate_at_primal_gradient hψ hx hdiff
  have hmin : IsLocalMin
      (fun u : E => Duality.conjugate D ψ u - ⟪x, u⟫_ℝ)
      (gradientWithin ψ D x) := by
    apply Filter.Eventually.of_forall
    intro u
    dsimp only
    have hlower := Duality.le_conjugate (hfinite u) hx
    rw [hattain]
    linarith [real_inner_comm x u, real_inner_comm x (gradientWithin ψ D x)]
  have hzero := hmin.hasFDerivAt_eq_zero
    (hdualdiff.hasGradientAt.hasFDerivAt.sub (innerSL ℝ x).hasFDerivAt)
  have heval := congrArg
    (fun L : E →L[ℝ] ℝ =>
      L (gradient (Duality.conjugate D ψ) (gradientWithin ψ D x) - x)) hzero
  simp only [sub_apply, zero_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply] at heval
  have hself :
      ⟪gradient (Duality.conjugate D ψ) (gradientWithin ψ D x) - x,
        gradient (Duality.conjugate D ψ) (gradientWithin ψ D x) - x⟫_ℝ = 0 := by
    simpa only [inner_sub_left] using heval
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

end AltOMD.InitialDuality
