import AltOMD.Entropy.Duality

/-!
# Exact primal mirror steps and accumulated dual variables

A primal minimizer determines the conjugate gradient at the updated dual point.
The dual representative can contain normal components on a lower-dimensional
primal domain: only its action on feasible differences must agree with the
relative primal gradient. No feasibility or differentiability assumption at the
next conjugate gradient is required for this implication.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD.PrimalDualStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every attained conjugate value determines its gradient wherever the conjugate
is differentiable. This only uses the defining supremum and Fermat's theorem. -/
theorem gradient_conjugate_eq_of_attains {D : Set E} {ψ : E → ℝ} {u y : E}
    (hfinite : ∀ v, v ∈ Duality.dualDomain D ψ)
    (hy : y ∈ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u)
    (hattain : Duality.conjugate D ψ u = ⟪u, y⟫_ℝ - ψ y) :
    gradient (Duality.conjugate D ψ) u = y := by
  have hmin : IsLocalMin
      (fun v : E => Duality.conjugate D ψ v - ⟪y, v⟫_ℝ) u := by
    apply Filter.Eventually.of_forall
    intro v
    dsimp only
    have hlower := Duality.le_conjugate (hfinite v) hy
    rw [hattain]
    linarith [real_inner_comm y v, real_inner_comm y u]
  have hzero := hmin.hasFDerivAt_eq_zero
    (hdualdiff.hasGradientAt.hasFDerivAt.sub (innerSL ℝ y).hasFDerivAt)
  have heval := congrArg
    (fun L : E →L[ℝ] ℝ => L (gradient (Duality.conjugate D ψ) u - y)) hzero
  simp only [sub_apply, zero_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply] at heval
  have hself : ⟪gradient (Duality.conjugate D ψ) u - y,
      gradient (Duality.conjugate D ψ) u - y⟫_ℝ = 0 := by
    simpa only [inner_sub_left] using heval
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- On the feasible set the mirror objective and the negative conjugate objective
differ by a constant. The accumulated dual variable need not equal an arbitrarily
chosen ambient representative of the relative primal gradient. -/
theorem mirror_objective_eq_of_stationarity {D : Set E} {ψ : E → ℝ}
    {u g x a y : E} {η : ℝ}
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0) (hy : y ∈ D) :
    η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x =
      ψ y - ⟪u - η • a, y⟫_ℝ + (⟪u, x⟫_ℝ - ψ x) := by
  have hs := hstationary y hy
  simp only [inner_sub_left, inner_sub_right] at hs
  simp only [Duality.bregman, inner_sub_right, inner_sub_left, real_inner_smul_left]
  linarith

/-- A feasible primal mirror minimizer attains the conjugate supremum at the
updated accumulated dual variable. -/
theorem conjugate_attained_of_mirror_minimizer {D : Set E} {ψ : E → ℝ}
    {u g x a y : E} {η : ℝ}
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0) (hy : y ∈ D)
    (hmin : ∀ c ∈ D,
      η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x ≤
        η * ⟪a, c⟫_ℝ + Duality.bregman ψ g c x) :
    Duality.conjugate D ψ (u - η • a) = ⟪u - η • a, y⟫_ℝ - ψ y := by
  have hmax (c : E) (hc : c ∈ D) :
      ⟪u - η • a, c⟫_ℝ - ψ c ≤ ⟪u - η • a, y⟫_ℝ - ψ y := by
    have h := hmin c hc
    rw [mirror_objective_eq_of_stationarity hstationary hy,
      mirror_objective_eq_of_stationarity hstationary hc] at h
    linarith
  have hfinite : u - η • a ∈ Duality.dualDomain D ψ := by
    refine ⟨⟪u - η • a, y⟫_ℝ - ψ y, ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact hmax c hc
  exact le_antisymm (Duality.conjugate_le ⟨y, hy⟩ hmax)
    (Duality.le_conjugate hfinite hy)

/-- A primal mirror minimizer is exactly the next conjugate gradient, without
assuming that next gradient is feasible or that the primal regularizer is
differentiable there. -/
theorem mirror_step_gradient_update_of_stationarity {D : Set E} {ψ : E → ℝ}
    {u g x a y : E} {η : ℝ}
    (hfinite : ∀ v, v ∈ Duality.dualDomain D ψ)
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0)
    (hy : y ∈ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (u - η • a))
    (hmin : ∀ c ∈ D,
      η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x ≤
        η * ⟪a, c⟫_ℝ + Duality.bregman ψ g c x) :
    gradient (Duality.conjugate D ψ) (u - η • a) = y :=
  gradient_conjugate_eq_of_attains hfinite hy hdualdiff
    (conjugate_attained_of_mirror_minimizer hstationary hy hmin)

/-- Exact primal-to-dual mirror-step correspondence for a relative-interior
current iterate represented by an arbitrary accumulated dual variable. -/
theorem mirror_step_gradient_update {D : Set E} {ψ : E → ℝ}
    {u x a y : E} {η : ℝ}
    (hψ : ConvexOn ℝ D ψ)
    (hfinite : ∀ v, v ∈ Duality.dualDomain D ψ)
    (hx : x ∈ intrinsicInterior ℝ D)
    (hψdiff : DifferentiableWithinAt ℝ ψ D x)
    (hxdual : gradient (Duality.conjugate D ψ) u = x)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u)
    (hnextdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (u - η • a))
    (hy : y ∈ D)
    (hmin : ∀ c ∈ D,
      η * ⟪a, y⟫_ℝ + Duality.bregman ψ (gradientWithin ψ D x) y x ≤
        η * ⟪a, c⟫_ℝ + Duality.bregman ψ (gradientWithin ψ D x) c x) :
    gradient (Duality.conjugate D ψ) (u - η • a) = y := by
  subst x
  exact mirror_step_gradient_update_of_stationarity hfinite
    (Duality.identities_of_differentiable hψ hx hψdiff (hfinite u) hdualdiff).2
    hy hnextdualdiff hmin

/-- Conversely, an attained conjugate value gives a primal mirror minimizer for
any dual representative agreeing with the relative gradient on feasible directions. -/
theorem mirror_step_minimizes_of_attains {D : Set E} {ψ : E → ℝ}
    {u g x a y : E} {η : ℝ}
    (hfinite : u - η • a ∈ Duality.dualDomain D ψ)
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0)
    (hy : y ∈ D)
    (hattain : Duality.conjugate D ψ (u - η • a) = ⟪u - η • a, y⟫_ℝ - ψ y)
    {c : E} (hc : c ∈ D) :
    η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x ≤
      η * ⟪a, c⟫_ℝ + Duality.bregman ψ g c x := by
  rw [mirror_objective_eq_of_stationarity hstationary hy,
    mirror_objective_eq_of_stationarity hstationary hc]
  have h := Duality.le_conjugate hfinite hc
  rw [hattain] at h
  linarith

end AltOMD.PrimalDualStep
