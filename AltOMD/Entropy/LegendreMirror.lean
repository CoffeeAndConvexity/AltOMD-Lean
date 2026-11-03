import AltOMD.Entropy.LegendreBoundary
import AltOMD.Entropy.ConjugateFeasibility

/-!
# Interior preservation for Legendre mirror updates

Boundary blowup is used through the proved absence of a finite supporting
functional at a relative-boundary point. Thus every feasible mirror minimizer
lies in the relative interior. Compactness and lower semicontinuity additionally
supply existence; differentiability of the conjugate supplies uniqueness.
-/

open Set
open scoped InnerProductSpace

namespace AltOMD.LegendreMirror

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every feasible minimizer of a linear perturbation of the regularizer is
interior. The gradient representative and base point in the Bregman expression
are arbitrary; no interiority or differentiability of the proposed next point
is assumed. -/
theorem mirror_minimizer_mem_intrinsicInterior {D : Set E} {ψ : E → ℝ}
    {p x g a y : E} {η : ℝ}
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D) (hy : y ∈ D)
    (hmin : IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D y) :
    y ∈ intrinsicInterior ℝ D := by
  apply LegendreBoundary.mem_intrinsicInterior_of_support
    (q := innerSL ℝ (g - η • a)) hψ hdiff hsteep hp hy
  intro c hc
  have h := hmin hc
  simp only [Set.mem_setOf_eq, Duality.bregman, inner_sub_right] at h
  simp only [innerSL_apply_apply, inner_sub_left, inner_sub_right, real_inner_smul_left]
  linarith

/-- At every differentiability point the conjugate gradient is an interior
primal point. Compactness and lower semicontinuity supply its attainment, while
the Legendre blowup condition excludes a boundary maximizer. -/
theorem gradient_conjugate_mem_intrinsicInterior {D : Set E} {ψ : E → ℝ} {p u : E}
    (hcompact : IsCompact D) (hlsc : LowerSemicontinuousOn ψ D)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u) :
    gradient (Duality.conjugate D ψ) u ∈ intrinsicInterior ℝ D := by
  have hD : D.Nonempty := ⟨p, intrinsicInterior_subset hp⟩
  obtain ⟨hmem, hattain⟩ :=
    ConjugateFeasibility.gradient_mem_and_conjugate_eq hD hcompact hlsc hdualdiff
  apply LegendreBoundary.mem_intrinsicInterior_of_support
    (q := innerSL ℝ u) hψ hdiff hsteep hp hmem
  intro c hc
  have h := Duality.le_conjugate
    (ConjugateFeasibility.conjugate_finite hD hcompact hlsc u) hc
  rw [hattain] at h
  simp only [innerSL_apply_apply, inner_sub_right]
  linarith

/-- A conjugate-gradient mirror update is an interior, unique primal minimizer.
This applies to arbitrary accumulated dual representatives agreeing with the
primal gradient on feasible differences. -/
theorem compact_mirror_step_interior_of_stationarity
    {D : Set E} {ψ : E → ℝ} {p u g x a : E} {η : ℝ}
    (hcompact : IsCompact D) (hlsc : LowerSemicontinuousOn ψ D)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D)
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (u - η • a)) :
    gradient (Duality.conjugate D ψ) (u - η • a) ∈ intrinsicInterior ℝ D ∧
      IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D
        (gradient (Duality.conjugate D ψ) (u - η • a)) ∧
      ∀ y ∈ D,
        IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D y ↔
          y = gradient (Duality.conjugate D ψ) (u - η • a) := by
  have hD : D.Nonempty := ⟨p, intrinsicInterior_subset hp⟩
  obtain ⟨_, hmin, huniq⟩ :=
    ConjugateFeasibility.compact_mirror_step_of_stationarity
      hD hcompact hlsc hstationary hdualdiff
  exact ⟨gradient_conjugate_mem_intrinsicInterior
    hcompact hlsc hψ hdiff hsteep hp hdualdiff, hmin, huniq⟩

/-- The usual primal mirror step exists, is unique, and stays in the relative
interior. Its base point only enters through the chosen Bregman gradient. -/
theorem compact_mirror_step_interior {D : Set E} {ψ : E → ℝ}
    {p x g a : E} {η : ℝ}
    (hcompact : IsCompact D) (hlsc : LowerSemicontinuousOn ψ D)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (g - η • a)) :
    gradient (Duality.conjugate D ψ) (g - η • a) ∈ intrinsicInterior ℝ D ∧
      IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D
        (gradient (Duality.conjugate D ψ) (g - η • a)) ∧
      ∀ y ∈ D,
        IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D y ↔
          y = gradient (Duality.conjugate D ψ) (g - η • a) := by
  exact compact_mirror_step_interior_of_stationarity
    hcompact hlsc hψ hdiff hsteep hp (by intro c hc; simp) hdualdiff

end AltOMD.LegendreMirror
