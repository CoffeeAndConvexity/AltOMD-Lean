import AltOMD.Entropy.Duality
import AltOMD.Entropy.RelativeInteriorGeometry
import Mathlib.Tactic.Abel

/-!
# Gradients relative to the affine hull

On a lower-dimensional domain an ambient derivative representative may contain
an arbitrary normal component. The relative gradient represents the derivative
restricted to the direction space of the affine hull. Its norm is exactly the
operator norm of that restricted derivative. At relative-interior points,
these definitions agree with differentiation in affine-hull coordinates.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Riesz representative of the differential restricted to directions in
the affine hull of the domain. Completeness of the direction space follows,
in particular, in the finite-dimensional setting of the paper. -/
noncomputable def relativeGradient (D : Set E) (ψ : E → ℝ) (x : E)
    [CompleteSpace (affineSpan ℝ D).direction] : (affineSpan ℝ D).direction :=
  (InnerProductSpace.toDual ℝ (affineSpan ℝ D).direction).symm
    ((fderivWithin ℝ ψ D x).comp (affineSpan ℝ D).direction.subtypeL)

/-- The paper's relative-gradient norm is the restricted derivative's operator
norm. This equality excludes arbitrary ambient normal components. -/
theorem norm_relativeGradient (D : Set E) (ψ : E → ℝ) (x : E)
    [CompleteSpace (affineSpan ℝ D).direction] :
    ‖relativeGradient D ψ x‖ =
      ‖(fderivWithin ℝ ψ D x).comp (affineSpan ℝ D).direction.subtypeL‖ :=
  (InnerProductSpace.toDual ℝ (affineSpan ℝ D).direction).symm.norm_map _

/-- The relative gradient represents the actual within-domain differential in
every affine-hull direction. -/
theorem inner_relativeGradient (D : Set E) (ψ : E → ℝ) (x : E)
    [CompleteSpace (affineSpan ℝ D).direction] (v : (affineSpan ℝ D).direction) :
    ⟪relativeGradient D ψ x, v⟫_ℝ = fderivWithin ℝ ψ D x (v : E) :=
  InnerProductSpace.toDual_symm_apply

/-- A within-domain differential is the ordinary differential of the function
in affine-hull coordinates at a relative-interior point. -/
theorem hasFDerivAt_affineChart {D : Set E} {ψ : E → ℝ} {x : E}
    {g : E →L[ℝ] ℝ} (hx : x ∈ intrinsicInterior ℝ D)
    (hg : HasFDerivWithinAt ψ g D x) :
    HasFDerivAt (fun v : (affineSpan ℝ D).direction => ψ (x + (v : E)))
      (g.comp (affineSpan ℝ D).direction.subtypeL) 0 := by
  have hchart : HasFDerivAt
      (fun v : (affineSpan ℝ D).direction => x + (v : E))
      (affineSpan ℝ D).direction.subtypeL 0 := by
    exact (affineSpan ℝ D).direction.subtypeL.hasFDerivAt.const_add x
  simpa only [Function.comp_def] using hg.comp_hasFDerivAt_of_eq
    (0 : (affineSpan ℝ D).direction) hchart
    (RelativeInteriorGeometry.eventually_add_mem hx) (by simp)

/-- Restriction to the affine directions removes all ambiguity in an ambient
within-domain derivative at a relative-interior point. -/
theorem restricted_fderivWithin_eq {D : Set E} {ψ : E → ℝ} {x : E}
    {g : E →L[ℝ] ℝ} (hx : x ∈ intrinsicInterior ℝ D)
    (hg : HasFDerivWithinAt ψ g D x) :
    (fderivWithin ℝ ψ D x).comp (affineSpan ℝ D).direction.subtypeL =
      g.comp (affineSpan ℝ D).direction.subtypeL :=
  (hasFDerivAt_affineChart hx hg.differentiableWithinAt.hasFDerivWithinAt).unique
    (hasFDerivAt_affineChart hx hg)

/-- The defined relative gradient is the actual gradient in affine-hull
coordinates; this proves that the definition uses the paper's derivative. -/
theorem hasGradientAt_relativeGradient {D : Set E} {ψ : E → ℝ} {x : E}
    [CompleteSpace (affineSpan ℝ D).direction]
    (hx : x ∈ intrinsicInterior ℝ D) (hψ : DifferentiableWithinAt ℝ ψ D x) :
    HasGradientAt (fun v : (affineSpan ℝ D).direction => ψ (x + (v : E)))
      (relativeGradient D ψ x) 0 := by
  rw [hasGradientAt_iff_hasFDerivAt, relativeGradient,
    LinearIsometryEquiv.apply_symm_apply]
  exact hasFDerivAt_affineChart hx hψ.hasFDerivWithinAt

/-- Equality with mathlib's ordinary gradient of the translated affine
restriction gives a canonical, representation-independent relative gradient. -/
theorem relativeGradient_eq_gradient_affineChart {D : Set E} {ψ : E → ℝ} {x : E}
    [CompleteSpace (affineSpan ℝ D).direction]
    (hx : x ∈ intrinsicInterior ℝ D) (hψ : DifferentiableWithinAt ℝ ψ D x) :
    relativeGradient D ψ x =
      gradient (fun v : (affineSpan ℝ D).direction => ψ (x + (v : E))) 0 :=
  (hasGradientAt_relativeGradient hx hψ).gradient.symm

/-- A derivative in affine-hull coordinates extends to a within-domain ambient
derivative by composing with orthogonal projection. Thus relative smoothness
does not impose an additional ambient differentiability assumption. -/
theorem differentiableWithinAt_of_affineChart {D : Set E} {ψ : E → ℝ} {x : E}
    [CompleteSpace (affineSpan ℝ D).direction] (hx : x ∈ D)
    (hψ : DifferentiableAt ℝ
      (fun v : (affineSpan ℝ D).direction => ψ (x + (v : E))) 0) :
    DifferentiableWithinAt ℝ ψ D x := by
  let K := (affineSpan ℝ D).direction
  have hproj : DifferentiableAt ℝ (fun y : E => K.orthogonalProjectionOnto (y - x)) x :=
    K.orthogonalProjectionOnto.differentiableAt.comp x
      (differentiableAt_id.sub_const x)
  have hψ' : DifferentiableAt ℝ (fun v : K => ψ (x + (v : E)))
      (K.orthogonalProjectionOnto (x - x)) := by simpa using hψ
  have hfull : DifferentiableAt ℝ
      (fun y : E => ψ (x + (K.orthogonalProjectionOnto (y - x) : E))) x := by
    simpa only [Function.comp_def] using hψ'.comp x hproj
  have hproj_eq (y : E) (hy : y ∈ D) :
      (K.orthogonalProjectionOnto (y - x) : E) = y - x := by
    change K.starProjection (y - x) = y - x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ D hy) (subset_affineSpan ℝ D hx)
  apply hfull.differentiableWithinAt.congr
  · intro y hy
    rw [hproj_eq y hy]
    congr 1
    abel
  · simp

/-- At relative-interior points the ambient within-domain formulation is
exactly differentiability of the affine restriction used in the paper. -/
theorem differentiableWithinAt_iff_affineChart {D : Set E} {ψ : E → ℝ} {x : E}
    [CompleteSpace (affineSpan ℝ D).direction]
    (hx : x ∈ intrinsicInterior ℝ D) :
    DifferentiableWithinAt ℝ ψ D x ↔
      DifferentiableAt ℝ (fun v : (affineSpan ℝ D).direction => ψ (x + (v : E))) 0 := by
  constructor
  · intro hψ
    exact (hasFDerivAt_affineChart hx hψ.hasFDerivWithinAt).differentiableAt
  · exact differentiableWithinAt_of_affineChart (intrinsicInterior_subset hx)

end AltOMD
