import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Linarith

/-!
# Convex duality on a possibly lower-dimensional domain

The conjugate is the supremum over the effective domain. Its finiteness is
recorded by boundedness of that supremum, rather than by assigning an arbitrary
real value to an infinite conjugate. All supporting inequalities below follow
from convexity and actual derivatives.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD.Duality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable convex function lies above its tangent functional, including
when the domain has empty ambient interior. -/
theorem supporting_inequality {D : Set E} {ψ : E → ℝ} {x y : E}
    {g : E →L[ℝ] ℝ} (hψ : ConvexOn ℝ D ψ) (hx : x ∈ D) (hy : y ∈ D)
    (hderiv : HasFDerivWithinAt ψ g D x) :
    ψ x + g (y - x) ≤ ψ y := by
  have hconv := hψ.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasDerivWithinAt (ψ ∘ AffineMap.lineMap x y) (g (y - x))
      ((AffineMap.lineMap x y) ⁻¹' D) (0 : ℝ) :=
    hderiv.comp_hasDerivWithinAt_of_eq (0 : ℝ) AffineMap.hasDerivWithinAt_lineMap
      (mapsTo_preimage _ _) (by simp)
  have hs := hconv.le_slope_of_hasDerivWithinAt
    (by simpa using hx) (by simpa using hy) (zero_lt_one : (0 : ℝ) < 1) hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hs
  linarith

/-- The scalar values whose supremum is the conjugate restricted to `D`. -/
def conjugateValues (D : Set E) (ψ : E → ℝ) (u : E) : Set ℝ :=
  (fun y => ⟪u, y⟫_ℝ - ψ y) '' D

/-- The conjugate, used only at points where `conjugateValues` is bounded above. -/
noncomputable def conjugate (D : Set E) (ψ : E → ℝ) (u : E) : ℝ :=
  sSup (conjugateValues D ψ u)

/-- The effective domain of the conjugate. -/
def dualDomain (D : Set E) (ψ : E → ℝ) : Set E :=
  {u | BddAbove (conjugateValues D ψ u)}

theorem le_conjugate {D : Set E} {ψ : E → ℝ} {u x : E}
    (hu : u ∈ dualDomain D ψ) (hx : x ∈ D) :
    ⟪u, x⟫_ℝ - ψ x ≤ conjugate D ψ u :=
  le_csSup hu ⟨x, hx, rfl⟩

theorem conjugate_le {D : Set E} {ψ : E → ℝ} (hD : D.Nonempty)
    {u : E} {b : ℝ} (hb : ∀ y ∈ D, ⟪u, y⟫_ℝ - ψ y ≤ b) :
    conjugate D ψ u ≤ b := by
  apply csSup_le (hD.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hb y hy

private theorem conjugate_combo_bound {D : Set E} {ψ : E → ℝ} {u v : E}
    (hu : u ∈ dualDomain D ψ) (hv : v ∈ dualDomain D ψ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {y : E} (hy : y ∈ D) :
    ⟪a • u + b • v, y⟫_ℝ - ψ y ≤
      a * conjugate D ψ u + b * conjugate D ψ v := by
  calc
    ⟪a • u + b • v, y⟫_ℝ - ψ y =
        a * (⟪u, y⟫_ℝ - ψ y) + b * (⟪v, y⟫_ℝ - ψ y) := by
      simp only [inner_add_left, real_inner_smul_left]
      have hscaled := congrArg (fun t : ℝ => t * ψ y) hab
      nlinarith [hscaled]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_conjugate hu hy) ha)
      (mul_le_mul_of_nonneg_left (le_conjugate hv hy) hb)

/-- Finiteness of the conjugate is preserved by convex combinations. -/
theorem convex_dualDomain (D : Set E) (ψ : E → ℝ) : Convex ℝ (dualDomain D ψ) := by
  intro u hu v hv a b ha hb hab
  refine ⟨a * conjugate D ψ u + b * conjugate D ψ v, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact conjugate_combo_bound hu hv ha hb hab hy

/-- Convexity of the conjugate follows directly from its defining supremum. -/
theorem convexOn_conjugate {D : Set E} (ψ : E → ℝ) (hD : D.Nonempty) :
    ConvexOn ℝ (dualDomain D ψ) (conjugate D ψ) := by
  refine ⟨convex_dualDomain D ψ, ?_⟩
  intro u hu v hv a b ha hb hab
  exact conjugate_le hD (fun y hy => conjugate_combo_bound hu hv ha hb hab hy)

/-- Fenchel equality from convexity, a derivative on the primal domain, and the
derivative of the conjugate. No Fenchel equality or support inequality is assumed. -/
theorem fenchel_equality {D : Set E} {ψ : E → ℝ} {u x g : E}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ D)
    (hψderiv : HasFDerivWithinAt ψ (innerSL ℝ g) D x)
    (hu : u ∈ dualDomain D ψ)
    (hdualderiv : HasFDerivAt (conjugate D ψ) (innerSL ℝ x) u) :
    ψ x + conjugate D ψ u = ⟪u, x⟫_ℝ := by
  have hs (y : E) (hy : y ∈ D) :
      ⟪g, y⟫_ℝ - ψ y ≤ ⟪g, x⟫_ℝ - ψ x := by
    have h := supporting_inequality hψ hx hy hψderiv
    simp only [innerSL_apply_apply, inner_sub_right] at h
    linarith
  have hg : g ∈ dualDomain D ψ := by
    refine ⟨⟪g, x⟫_ℝ - ψ x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hs y hy
  have hconjg : conjugate D ψ g = ⟪g, x⟫_ℝ - ψ x :=
    le_antisymm (conjugate_le ⟨x, hx⟩ hs) (le_conjugate hg hx)
  have hsupport := supporting_inequality (convexOn_conjugate ψ ⟨x, hx⟩)
    hu hg hdualderiv.hasFDerivWithinAt
  rw [hconjg] at hsupport
  simp only [innerSL_apply_apply, inner_sub_right] at hsupport
  have hux : ⟪x, u⟫_ℝ = ⟪u, x⟫_ℝ := real_inner_comm _ _
  have hgx : ⟪x, g⟫_ℝ = ⟪g, x⟫_ℝ := real_inner_comm _ _
  have hlower := le_conjugate hu hx
  linarith

/-- Relative interior supplies a two-sided interval in every feasible direction. -/
theorem eventually_lineMap_mem {D : Set E} {x c : E}
    (hx : x ∈ intrinsicInterior ℝ D) (hc : c ∈ D) :
    ∀ᶠ t : ℝ in 𝓝 0, AffineMap.lineMap x c t ∈ D := by
  rcases mem_intrinsicInterior.mp hx with ⟨x₀, hx₀, rfl⟩
  let l : ℝ → affineSpan ℝ D := fun t =>
    ⟨AffineMap.lineMap (x₀ : E) c t,
      AffineMap.lineMap_mem t x₀.property (subset_affineSpan ℝ D hc)⟩
  have hl : Continuous l := AffineMap.lineMap_continuous.subtype_mk _
  have hlzero : l 0 = x₀ := by
    apply Subtype.ext
    simp [l]
  have hnbhd : ((↑) ⁻¹' D : Set (affineSpan ℝ D)) ∈ 𝓝 (l 0) := by
    rw [hlzero]
    exact mem_interior_iff_mem_nhds.mp hx₀
  exact hl.continuousAt hnbhd

/-- At a relative-interior maximizer, the dual variable and the primal gradient
agree on every direction in the effective domain. -/
theorem relative_stationarity {D : Set E} {ψ : E → ℝ} {u x g : E}
    (hx : x ∈ intrinsicInterior ℝ D)
    (hψderiv : HasFDerivWithinAt ψ (innerSL ℝ g) D x)
    (hmax : ∀ y ∈ D, ⟪u, y⟫_ℝ - ψ y ≤ ⟪u, x⟫_ℝ - ψ x)
    {c : E} (hc : c ∈ D) :
    ⟪u - g, c - x⟫_ℝ = 0 := by
  have hline := eventually_lineMap_mem hx hc
  have hψline : HasDerivAt (ψ ∘ AffineMap.lineMap x c) ⟪g, c - x⟫_ℝ (0 : ℝ) := by
    exact hψderiv.comp_hasDerivAt_of_eq (0 : ℝ)
      AffineMap.hasDerivAt_lineMap hline (by simp)
  have huline : HasDerivAt (fun t : ℝ => ⟪u, AffineMap.lineMap x c t⟫_ℝ)
      ⟪u, c - x⟫_ℝ 0 := by
    exact (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := c))
  have hlocal : IsLocalMax
      (fun t : ℝ => ⟪u, AffineMap.lineMap x c t⟫_ℝ - ψ (AffineMap.lineMap x c t)) 0 := by
    filter_upwards [hline] with t ht
    simpa using hmax (AffineMap.lineMap x c t) ht
  simpa only [inner_sub_left] using hlocal.hasDerivAt_eq_zero (huline.sub hψline)

/-- The manuscript's Fenchel--Legendre identities, allowing lower-dimensional
domains and using actual convexity and derivatives as hypotheses. -/
theorem fenchel_legendre_identities {D : Set E} {ψ : E → ℝ} {u x g : E}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ intrinsicInterior ℝ D)
    (hψderiv : HasFDerivWithinAt ψ (innerSL ℝ g) D x)
    (hu : u ∈ dualDomain D ψ)
    (hdualderiv : HasFDerivAt (conjugate D ψ) (innerSL ℝ x) u) :
    ψ x + conjugate D ψ u = ⟪u, x⟫_ℝ ∧
      ∀ c ∈ D, ⟪u - g, c - x⟫_ℝ = 0 := by
  have heq := fenchel_equality hψ (intrinsicInterior_subset hx) hψderiv hu hdualderiv
  refine ⟨heq, fun c hc => relative_stationarity hx hψderiv ?_ hc⟩
  intro y hy
  have h := le_conjugate hu hy
  linarith

/-- The Fenchel coupling at a comparator. -/
noncomputable def fenchelCoupling (D : Set E) (ψ : E → ℝ) (c u : E) : ℝ :=
  ψ c + conjugate D ψ u - ⟪u, c⟫_ℝ

/-- Bregman divergence with an explicitly supplied relative gradient. -/
def bregman (ψ : E → ℝ) (g c x : E) : ℝ :=
  ψ c - ψ x - ⟪g, c - x⟫_ℝ

/-- The Fenchel coupling equals the Bregman divergence at the conjugate gradient. -/
theorem fenchelCoupling_eq_bregman {D : Set E} {ψ : E → ℝ} {u x g c : E}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ intrinsicInterior ℝ D)
    (hψderiv : HasFDerivWithinAt ψ (innerSL ℝ g) D x)
    (hu : u ∈ dualDomain D ψ)
    (hdualderiv : HasFDerivAt (conjugate D ψ) (innerSL ℝ x) u)
    (hc : c ∈ D) :
    fenchelCoupling D ψ c u = bregman ψ g c x := by
  obtain ⟨heq, hstationary⟩ := fenchel_legendre_identities hψ hx hψderiv hu hdualderiv
  have hs := hstationary c hc
  simp only [inner_sub_left, inner_sub_right] at hs
  simp only [fenchelCoupling, bregman, inner_sub_right]
  linarith

theorem fenchelCoupling_nonneg {D : Set E} {ψ : E → ℝ} {u c : E}
    (hu : u ∈ dualDomain D ψ) (hc : c ∈ D) :
    0 ≤ fenchelCoupling D ψ c u := by
  have h := le_conjugate hu hc
  unfold fenchelCoupling
  linarith

/-- A formulation using mathlib's actual gradient operators. Relative
differentiability is expressed by `DifferentiableWithinAt`; no uniqueness of an
ambient derivative is needed on a lower-dimensional domain. -/
theorem identities_of_differentiable [CompleteSpace E]
    {D : Set E} {ψ : E → ℝ} {u : E}
    (hψ : ConvexOn ℝ D ψ)
    (hx : gradient (conjugate D ψ) u ∈ intrinsicInterior ℝ D)
    (hψdiff : DifferentiableWithinAt ℝ ψ D (gradient (conjugate D ψ) u))
    (hu : u ∈ dualDomain D ψ)
    (hdualdiff : DifferentiableAt ℝ (conjugate D ψ) u) :
    ψ (gradient (conjugate D ψ) u) + conjugate D ψ u =
        ⟪u, gradient (conjugate D ψ) u⟫_ℝ ∧
      ∀ c ∈ D, ⟪u - gradientWithin ψ D (gradient (conjugate D ψ) u),
        c - gradient (conjugate D ψ) u⟫_ℝ = 0 := by
  exact fenchel_legendre_identities hψ hx
    hψdiff.hasGradientWithinAt.hasFDerivWithinAt hu
    hdualdiff.hasGradientAt.hasFDerivAt

end AltOMD.Duality
