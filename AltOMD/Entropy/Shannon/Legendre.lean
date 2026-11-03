import AltOMD.Entropy.Shannon.Extended
import AltOMD.Regret.ExtendedRegret

/-!
# The extended-real Shannon entropy is Legendre

The finite values agree with real entropy on the simplex. This equality
transports strict convexity and relative-gradient blowup; local agreement
in affine-hull coordinates supplies the relative C¹ condition.
-/

open Set Filter
open scoped Topology ContDiff

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι]

/-- The finite restriction of extended entropy agrees with entropy on its domain. -/
theorem value_extendedEntropy_eqOn :
    EqOn (ExtendedDuality.value (extendedEntropy : EuclideanSpace ℝ ι → EReal))
      entropy simplex := by
  intro x hx
  simp only [ExtendedDuality.value, extendedEntropy_of_mem hx, EReal.toReal_coe]

private theorem convex_intrinsicInterior_simplex :
    Convex ℝ (intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι))) := by
  intro x hx y hy a b ha hb hab
  apply positive_mem_intrinsicInterior
    (convex_simplex (intrinsicInterior_subset hx) (intrinsicInterior_subset hy) ha hb hab)
  intro i
  have hxpos := positive_of_mem_intrinsicInterior hx i
  have hypos := positive_of_mem_intrinsicInterior hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hypos
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hxpos)
      (mul_nonneg hb hypos.le)

/-- Shannon entropy satisfies the bundled relative Legendre condition used by
the main theorem for extended-real regularizers. -/
theorem isLegendre_extendedEntropy [Nonempty ι] :
    ExtendedRegret.IsLegendre (extendedEntropy : EuclideanSpace ℝ ι → EReal) := by
  have hdomain : ExtendedDuality.domain (extendedEntropy : EuclideanSpace ℝ ι → EReal) =
      simplex := effectiveDomain_extendedEntropy
  refine ⟨extendedEntropy_proper, lowerSemicontinuous_extendedEntropy,
    convex_epigraph_extendedEntropy, ?_, ?_, ?_⟩
  · rw [hdomain]
    apply (strictConvexOn_entropy.subset intrinsicInterior_subset
      convex_intrinsicInterior_simplex).congr
    intro x hx
    exact (value_extendedEntropy_eqOn (intrinsicInterior_subset hx)).symm
  · rw [hdomain]
    intro z hz
    have hchart : ContDiffAt ℝ 1
        (fun v : (affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))).direction =>
          z + (v : EuclideanSpace ℝ ι)) 0 :=
      contDiffAt_const.add
        (affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))).direction.subtypeL.contDiff.contDiffAt
    have hsmooth : ContDiffAt ℝ 1
        (fun v : (affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))).direction =>
          entropy (z + (v : EuclideanSpace ℝ ι))) 0 := by
      have hentropy := (contDiffAt_entropy (positive_of_mem_intrinsicInterior hz)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
      apply ContDiffAt.comp (g := entropy) 0 ?_ hchart
      simpa only [ZeroMemClass.coe_zero, add_zero] using hentropy
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [RelativeInteriorGeometry.eventually_add_mem hz] with v hv
    exact value_extendedEntropy_eqOn hv
  · rw [hdomain]
    intro x hx hnot z hz htend
    have hgrad (n : ℕ) :
        relativeGradient simplex (ExtendedDuality.value extendedEntropy) (z n) =
          relativeGradient simplex entropy (z n) := by
      unfold relativeGradient
      rw [fderivWithin_congr' value_extendedEntropy_eqOn (intrinsicInterior_subset (hz n))]
    simpa only [hgrad] using gradientBlowsUpAtBoundary_entropy x hx hnot z hz htend

end AltOMD.Shannon
