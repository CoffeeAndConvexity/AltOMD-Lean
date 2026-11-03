import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Linarith

/-!
# Local geometry of the relative interior

The relative interior contains a neighborhood in the direction space of the
affine hull. These elementary facts do not require finite dimensionality or
compactness of the feasible set.
-/

open Set Filter
open scoped Topology

namespace AltOMD.RelativeInteriorGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A relative-interior point can be perturbed by all sufficiently small
vectors parallel to the affine hull. -/
theorem eventually_add_mem {D : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ D) :
    ∀ᶠ v : (affineSpan ℝ D).direction in 𝓝 0, p + (v : E) ∈ D := by
  rcases mem_intrinsicInterior.mp hp with ⟨p₀, hp₀, rfl⟩
  let l : (affineSpan ℝ D).direction → affineSpan ℝ D := fun v =>
    ⟨(p₀ : E) + (v : E), by
      simpa only [vadd_eq_add, add_comm] using
        AffineSubspace.vadd_mem_of_mem_direction v.property p₀.property⟩
  have hl : Continuous l :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  have hlzero : l 0 = p₀ := by
    apply Subtype.ext
    simp [l]
  have hnbhd : ((↑) ⁻¹' D : Set (affineSpan ℝ D)) ∈ 𝓝 (l 0) := by
    rw [hlzero]
    exact mem_interior_iff_mem_nhds.mp hp₀
  exact hl.continuousAt hnbhd

/-- Relative differentiability supplies a feasible closed relative ball on
which the regularizer has a uniform finite upper bound. -/
theorem exists_closedBall_bound {D : Set E} {ψ : E → ℝ} {p : E}
    (hp : p ∈ intrinsicInterior ℝ D)
    (hdiff : DifferentiableWithinAt ℝ ψ D p) :
    ∃ r > 0, ∀ v : (affineSpan ℝ D).direction, ‖v‖ ≤ r →
      p + (v : E) ∈ D ∧ ψ (p + (v : E)) ≤ ψ p + 1 := by
  have hmem := eventually_add_mem hp
  have hlim : Tendsto (fun v : (affineSpan ℝ D).direction => p + (v : E))
      (𝓝 0) (𝓝[D] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous
          (fun v : (affineSpan ℝ D).direction => p + (v : E)) :=
        continuous_const.add continuous_subtype_val
      simpa only [ContinuousAt, ZeroMemClass.coe_zero, add_zero] using
        hcont.continuousAt (x := 0)
    · exact hmem
  have hψlim : Tendsto ψ (𝓝[D] p) (𝓝 (ψ p)) := hdiff.continuousWithinAt
  have hupper : ∀ᶠ v : (affineSpan ℝ D).direction in 𝓝 0,
      ψ (p + (v : E)) < ψ p + 1 :=
    (hψlim.comp hlim) (Iio_mem_nhds (by linarith))
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (hmem.and hupper) with
    ⟨r, hr, hball⟩
  refine ⟨r, hr, fun v hv => ?_⟩
  have h := hball (by simpa using hv)
  exact ⟨h.1, h.2.le⟩

/-- Every point of the segment from a feasible point towards a
relative-interior point, except possibly its initial endpoint, is in the
relative interior. -/
theorem segment_mem_intrinsicInterior {D : Set E} {x p : E} {t : ℝ}
    (hD : Convex ℝ D) (hx : x ∈ D) (hp : p ∈ intrinsicInterior ℝ D)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    x + t • (p - x) ∈ intrinsicInterior ℝ D := by
  rcases mem_intrinsicInterior.mp hp with ⟨p₀, hp₀, rfl⟩
  have hxspan : x ∈ affineSpan ℝ D := subset_affineSpan ℝ D hx
  let z : affineSpan ℝ D :=
    ⟨AffineMap.lineMap x (p₀ : E) t,
      AffineMap.lineMap_mem t hxspan p₀.property⟩
  let q : affineSpan ℝ D → affineSpan ℝ D := fun y =>
    ⟨AffineMap.lineMap x (y : E) t⁻¹,
      AffineMap.lineMap_mem t⁻¹ hxspan y.property⟩
  have hq : Continuous q := by
    apply Continuous.subtype_mk
    change Continuous (fun y : affineSpan ℝ D => t⁻¹ • ((y : E) - x) + x)
    exact ((continuous_subtype_val.sub continuous_const).const_smul t⁻¹).add
      continuous_const
  have hqz : q z = p₀ := by
    apply Subtype.ext
    simp [q, z, ne_of_gt ht]
  have hnbhd : ((↑) ⁻¹' D : Set (affineSpan ℝ D)) ∈ 𝓝 (q z) := by
    rw [hqz]
    exact mem_interior_iff_mem_nhds.mp hp₀
  have hevent : ∀ᶠ y : affineSpan ℝ D in 𝓝 z, (q y : E) ∈ D :=
    hq.continuousAt hnbhd
  have hz : z ∈ interior ((↑) ⁻¹' D : Set (affineSpan ℝ D)) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hevent] with y hy
    have hcomb := hD.lineMap_mem hx hy ⟨ht.le, ht1⟩
    simpa [q, ne_of_gt ht] using hcomb
  have : (z : E) ∈ intrinsicInterior ℝ D :=
    mem_intrinsicInterior.mpr ⟨z, hz, rfl⟩
  simpa only [z, AffineMap.lineMap_apply_module', add_comm] using this

end AltOMD.RelativeInteriorGeometry
