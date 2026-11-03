import AltOMD.Entropy.PrimalDualStep
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Feasibility of the conjugate-gradient update

On a nonempty compact domain, lower semicontinuity of the regularizer makes
every conjugate supremum finite and attained. Differentiability of the conjugate
then identifies its gradient with this feasible maximizer. No inverse-gradient
mapping or feasibility assumption is needed for this conclusion.
-/

open Set
open scoped InnerProductSpace

namespace AltOMD.ConjugateFeasibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A lower semicontinuous regularizer on a nonempty compact domain has a
maximizer in the definition of its conjugate at every dual point. -/
theorem exists_conjugate_maximizer {D : Set E} {ψ : E → ℝ}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D) (u : E) :
    ∃ x ∈ D, ∀ y ∈ D, ⟪u, y⟫_ℝ - ψ y ≤ ⟪u, x⟫_ℝ - ψ x := by
  have hcont : Continuous (fun y : E => -⟪u, y⟫_ℝ) :=
    (innerSL ℝ u).continuous.neg
  have hsemi : LowerSemicontinuousOn (fun y => ψ y + -⟪u, y⟫_ℝ) D :=
    hψ.add hcont.continuousOn.lowerSemicontinuousOn
  obtain ⟨x, hx, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hD hcompact hsemi
  refine ⟨x, hx, ?_⟩
  intro y hy
  have h := (isMinOn_iff.mp hmin) y hy
  linarith

/-- Compactness and lower semicontinuity imply finiteness of the conjugate
everywhere; this finiteness is proved, rather than assumed. -/
theorem conjugate_finite {D : Set E} {ψ : E → ℝ}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D) (u : E) :
    u ∈ Duality.dualDomain D ψ := by
  obtain ⟨x, _, hmax⟩ := exists_conjugate_maximizer hD hcompact hψ u
  refine ⟨⟪u, x⟫_ℝ - ψ x, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hmax y hy

/-- The defining supremum of the conjugate is attained on the primal domain. -/
theorem exists_conjugate_eq {D : Set E} {ψ : E → ℝ}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D) (u : E) :
    ∃ x ∈ D, Duality.conjugate D ψ u = ⟪u, x⟫_ℝ - ψ x := by
  obtain ⟨x, hx, hmax⟩ := exists_conjugate_maximizer hD hcompact hψ u
  refine ⟨x, hx, le_antisymm (Duality.conjugate_le hD hmax) ?_⟩
  exact Duality.le_conjugate (conjugate_finite hD hcompact hψ u) hx

/-- The gradient of a differentiable conjugate belongs to the compact primal
domain and attains the defining supremum. Convexity and primal differentiability
are unnecessary for this feasibility statement. -/
theorem gradient_mem_and_conjugate_eq [CompleteSpace E]
    {D : Set E} {ψ : E → ℝ} {u : E}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u) :
    gradient (Duality.conjugate D ψ) u ∈ D ∧
      Duality.conjugate D ψ u =
        ⟪u, gradient (Duality.conjugate D ψ) u⟫_ℝ -
          ψ (gradient (Duality.conjugate D ψ) u) := by
  obtain ⟨x, hx, heq⟩ := exists_conjugate_eq hD hcompact hψ u
  have hgrad := PrimalDualStep.gradient_conjugate_eq_of_attains
    (conjugate_finite hD hcompact hψ) hx hdualdiff heq
  rw [hgrad]
  exact ⟨hx, heq⟩

/-- Every differentiability point of the conjugate gives a feasible primal
iterate under compactness and lower semicontinuity. -/
theorem gradient_mem [CompleteSpace E]
    {D : Set E} {ψ : E → ℝ} {u : E}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u) :
    gradient (Duality.conjugate D ψ) u ∈ D :=
  (gradient_mem_and_conjugate_eq hD hcompact hψ hdualdiff).1

/-- Compactness makes the conjugate-gradient update a feasible, unique primal
mirror minimizer whenever the current dual variable agrees with the primal
gradient on feasible differences. No property of the next primal iterate is
assumed. -/
theorem compact_mirror_step_of_stationarity [CompleteSpace E]
    {D : Set E} {ψ : E → ℝ} {u g x a : E} {η : ℝ}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hψ : LowerSemicontinuousOn ψ D)
    (hstationary : ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (u - η • a)) :
    gradient (Duality.conjugate D ψ) (u - η • a) ∈ D ∧
      IsMinOn (fun y => η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x) D
        (gradient (Duality.conjugate D ψ) (u - η • a)) ∧
      ∀ y ∈ D,
        IsMinOn (fun z => η * ⟪a, z⟫_ℝ + Duality.bregman ψ g z x) D y ↔
          y = gradient (Duality.conjugate D ψ) (u - η • a) := by
  have hfinite := conjugate_finite hD hcompact hψ
  obtain ⟨hnext, hattain⟩ := gradient_mem_and_conjugate_eq hD hcompact hψ hdualdiff
  have hmin : IsMinOn (fun y => η * ⟪a, y⟫_ℝ + Duality.bregman ψ g y x) D
      (gradient (Duality.conjugate D ψ) (u - η • a)) := by
    intro c hc
    exact PrimalDualStep.mirror_step_minimizes_of_attains
      (hfinite (u - η • a)) hstationary hnext hattain hc
  refine ⟨hnext, hmin, ?_⟩
  intro y hy
  constructor
  · intro hymin
    exact (PrimalDualStep.mirror_step_gradient_update_of_stationarity
      hfinite hstationary hy hdualdiff hymin).symm
  · rintro rfl
    exact hmin

/-- An actual relative-interior current iterate gives a feasible next iterate
and an exact equivalence between the primal mirror argmin and the accumulated
dual update. Compactness and lower semicontinuity supply existence; conjugate
differentiability supplies uniqueness. Neither feasibility nor primal
differentiability is assumed at the next iterate. -/
theorem compact_mirror_step [CompleteSpace E]
    {D : Set E} {ψ : E → ℝ} {u x a : E} {η : ℝ}
    (hD : D.Nonempty) (hcompact : IsCompact D)
    (hlsc : LowerSemicontinuousOn ψ D) (hψ : ConvexOn ℝ D ψ)
    (hx : x ∈ intrinsicInterior ℝ D)
    (hψdiff : DifferentiableWithinAt ℝ ψ D x)
    (hxdual : gradient (Duality.conjugate D ψ) u = x)
    (hdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) u)
    (hnextdualdiff : DifferentiableAt ℝ (Duality.conjugate D ψ) (u - η • a)) :
    gradient (Duality.conjugate D ψ) (u - η • a) ∈ D ∧
      IsMinOn (fun y => η * ⟪a, y⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D x) y x) D
        (gradient (Duality.conjugate D ψ) (u - η • a)) ∧
      ∀ y ∈ D,
        IsMinOn (fun z => η * ⟪a, z⟫_ℝ +
          Duality.bregman ψ (gradientWithin ψ D x) z x) D y ↔
          y = gradient (Duality.conjugate D ψ) (u - η • a) := by
  subst x
  exact compact_mirror_step_of_stationarity hD hcompact hlsc
    (Duality.identities_of_differentiable hψ hx hψdiff
      (conjugate_finite hD hcompact hlsc u) hdualdiff).2 hnextdualdiff

end AltOMD.ConjugateFeasibility
