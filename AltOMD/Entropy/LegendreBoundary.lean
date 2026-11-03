import AltOMD.Entropy.RelativeGradient
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# Legendre boundary exclusion

The gradient blowup condition is stated using the canonical gradient relative
to the affine hull. A finite supporting functional at a feasible boundary point
would bound these gradients along a segment approaching that point, contradicting
blowup. Thus every feasible point with a finite supporting functional is in the
relative interior.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD.LegendreBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A supporting functional at `x` bounds every relative derivative along the
segment from `x` to a relative ball on which the function is bounded above. -/
theorem restricted_derivative_bound {D : Set E} {ψ : E → ℝ}
    {x p : E} {q g : E →L[ℝ] ℝ} {r M t : ℝ}
    (hψ : ConvexOn ℝ D ψ) (hx : x ∈ D)
    (hsupport : ∀ c ∈ D, ψ x + q (c - x) ≤ ψ c)
    (hr : 0 < r)
    (hball : ∀ v : (affineSpan ℝ D).direction, ‖v‖ ≤ r →
      p + (v : E) ∈ D ∧ ψ (p + (v : E)) ≤ M)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : x + t • (p - x) ∈ D)
    (hderiv : HasFDerivWithinAt ψ g D (x + t • (p - x))) :
    ‖g.comp (affineSpan ℝ D).direction.subtypeL‖ ≤
      (M - ψ x - q (p - x)) / r := by
  have hsupportz := hsupport _ hz
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at hsupportz
  have hdx := Duality.supporting_inequality hψ hz hx hderiv
  have hxz : x - (x + t • (p - x)) = -(t • (p - x)) := by abel
  rw [hxz, map_neg, map_smul, smul_eq_mul] at hdx
  have hdir : q (p - x) ≤ g (p - x) := by
    by_contra h
    have hpos := mul_pos ht (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hupper (v : (affineSpan ℝ D).direction) (hv : ‖v‖ ≤ r) :
      g (v : E) ≤ M - ψ x - q (p - x) := by
    obtain ⟨hmem, hval⟩ := hball v hv
    have hdv := Duality.supporting_inequality hψ hz hmem hderiv
    have hdiff : p + (v : E) - (x + t • (p - x)) =
        (1 - t) • (p - x) + (v : E) := by
      rw [sub_smul, one_smul]
      abel
    rw [hdiff, map_add, map_smul, smul_eq_mul] at hdv
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hdir)]
  have hB : 0 ≤ M - ψ x - q (p - x) := by
    simpa using hupper 0 (by simpa using hr.le)
  have habs (v : (affineSpan ℝ D).direction) (hv : ‖v‖ ≤ r) :
      ‖g (v : E)‖ ≤ M - ψ x - q (p - x) := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hneg := hupper (-v) (by simpa using hv)
      simp only [Submodule.coe_neg, map_neg] at hneg
      linarith
    · exact hupper v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hB hr.le)
  intro v hv
  have hscaled := habs (r • v) (by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv])
  simp only [Submodule.coe_smul, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr] at hscaled
  change ‖g (v : E)‖ ≤ (M - ψ x - q (p - x)) / r
  apply (le_div_iff₀ hr).mpr
  simpa only [Real.norm_eq_abs, mul_comm] using hscaled

/-- The paper's Legendre steepness assumption, with gradients and boundary
taken relative to the affine hull. Every relative-interior sequence approaching
a relative-boundary point has gradient norm tending to infinity. -/
def GradientBlowsUpAtBoundary (D : Set E) (ψ : E → ℝ)
    [CompleteSpace (affineSpan ℝ D).direction] : Prop :=
  ∀ x ∈ closure D, x ∉ intrinsicInterior ℝ D →
    ∀ z : ℕ → E, (∀ n, z n ∈ intrinsicInterior ℝ D) →
      Tendsto z atTop (𝓝 x) →
        Tendsto (fun n => ‖relativeGradient D ψ (z n)‖) atTop atTop

/-- In the paper's finite-dimensional setting, the boundary used in the
steepness predicate is exactly mathlib's intrinsic (relative) frontier. -/
theorem gradientBlowsUpAtBoundary_iff_intrinsicFrontier
    [FiniteDimensional ℝ E] (D : Set E) (ψ : E → ℝ) :
    GradientBlowsUpAtBoundary D ψ ↔
      ∀ x ∈ intrinsicFrontier ℝ D,
        ∀ z : ℕ → E, (∀ n, z n ∈ intrinsicInterior ℝ D) →
          Tendsto z atTop (𝓝 x) →
            Tendsto (fun n => ‖relativeGradient D ψ (z n)‖) atTop atTop := by
  constructor
  · intro h x hx
    have hmem : x ∈ closure D \ intrinsicInterior ℝ D := by
      rwa [closure_sdiff_intrinsicInterior]
    exact h x hmem.1 hmem.2
  · intro h x hx hnot
    apply h x
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨hx, hnot⟩

/-- Under relative-gradient blowup, a feasible point admitting a finite
supporting functional is necessarily in the relative interior. -/
theorem mem_intrinsicInterior_of_support {D : Set E} {ψ : E → ℝ}
    [CompleteSpace (affineSpan ℝ D).direction] {p x : E} {q : E →L[ℝ] ℝ}
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D) (hx : x ∈ D)
    (hsupport : ∀ c ∈ D, ψ x + q (c - x) ≤ ψ c) :
    x ∈ intrinsicInterior ℝ D := by
  by_contra hboundary
  obtain ⟨r, hr, hball⟩ :=
    RelativeInteriorGeometry.exists_closedBall_bound hp (hdiff p hp)
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let z : ℕ → E := fun n => x + t n • (p - x)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hz (n : ℕ) : z n ∈ intrinsicInterior ℝ D :=
    RelativeInteriorGeometry.segment_mem_intrinsicInterior
      hψ.1 hx hp (ht n) (ht1 n)
  have htendsto : Tendsto t atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hztendsto : Tendsto z atTop (𝓝 x) := by
    simpa [z] using
      ((tendsto_const_nhds (x := x)).add
        (htendsto.smul (tendsto_const_nhds (x := p - x))))
  have hblow := hsteep x (subset_closure hx) hboundary z hz hztendsto
  have hbound (n : ℕ) :
      ‖relativeGradient D ψ (z n)‖ ≤ (ψ p + 1 - ψ x - q (p - x)) / r := by
    rw [norm_relativeGradient]
    exact restricted_derivative_bound hψ hx hsupport hr hball (ht n) (ht1 n)
      (intrinsicInterior_subset (hz n)) (hdiff (z n) (hz n)).hasFDerivWithinAt
  have hevent := (tendsto_atTop.1 hblow) ((ψ p + 1 - ψ x - q (p - x)) / r + 1)
  obtain ⟨n, hn⟩ := hevent.exists
  have := hbound n
  linarith

end AltOMD.LegendreBoundary
