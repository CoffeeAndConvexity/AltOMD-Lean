import AltOMD.Entropy.Shannon.Basic
import AltOMD.Entropy.LegendreBoundary
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Geometry and conjugacy of negative Shannon entropy

The effective domain is the closed simplex. The conjugacy theorem below uses
the actual supremum in `Duality.conjugate`, including comparators with zero
coordinates.
-/

open Set Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι]

theorem convex_simplex : Convex ℝ (simplex : Set (EuclideanSpace ℝ ι)) :=
  (convex_stdSimplex ℝ ι).linear_preimage (EuclideanSpace.equiv ι ℝ).toLinearMap

theorem isCompact_simplex : IsCompact (simplex : Set (EuclideanSpace ℝ ι)) := by
  have h := (isCompact_stdSimplex ℝ ι).image (EuclideanSpace.equiv ι ℝ).symm.continuous
  convert h using 1
  ext x
  simp only [Set.mem_image]
  constructor
  · intro hx
    exact ⟨(EuclideanSpace.equiv ι ℝ) x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem continuous_entropy : Continuous (entropy : EuclideanSpace ℝ ι → ℝ) := by
  unfold entropy
  exact continuous_finsetSum _ fun i _ => Real.continuous_mul_log.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

theorem convexOn_entropy : ConvexOn ℝ simplex (entropy : EuclideanSpace ℝ ι → ℝ) := by
  refine ⟨convex_simplex, ?_⟩
  intro x hx y hy a b ha hb hab
  have h (i : ι) := Real.convexOn_mul_log.2 (hx.1 i) (hy.1 i) ha hb hab
  simpa only [entropy, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum] using Finset.sum_le_sum (fun i _ => h i)

theorem strictConvexOn_entropy :
    StrictConvexOn ℝ simplex (entropy : EuclideanSpace ℝ ι → ℝ) := by
  refine ⟨convex_simplex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hi : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (by ext i; exact h i)
  obtain ⟨i, hi⟩ := hi
  have hle (j : ι) := Real.convexOn_mul_log.2 (hx.1 j) (hy.1 j) ha.le hb.le hab
  have hlt := Real.strictConvexOn_mul_log.2 (hx.1 i) (hy.1 i) hi ha hb hab
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hle j)
    ⟨i, Finset.mem_univ i, hlt⟩
  simpa only [entropy, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum] using hs

theorem entropy_hasFDerivAt {x : EuclideanSpace ℝ ι} (hx : ∀ i, 0 < x i) :
    HasFDerivAt entropy (innerSL ℝ (entropyGradient x)) x := by
  have h (i : ι) : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i * Real.log (y i))
      ((Real.log (x i) + 1) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    have hp : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i)
        (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    convert! hp.mul (hp.log (hx i).ne') using 1
    ext v
    simp [add_smul, smul_smul, (hx i).ne', add_comm]
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
  convert! hs using 1
  ext v
  simp [innerSL_apply_apply, PiLp.inner_apply, entropyGradient, add_comm, mul_comm]

theorem contDiffAt_entropy {x : EuclideanSpace ℝ ι} (hx : ∀ i, 0 < x i) :
    ContDiffAt ℝ ∞ entropy x := by
  unfold entropy
  apply ContDiffAt.sum
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.mul
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.log (hx i).ne')

theorem sum_eq_one_of_mem_affineSpan {x : EuclideanSpace ℝ ι}
    (hx : x ∈ affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))) :
    ∑ i, x i = 1 := by
  refine affineSpan_induction hx (fun y hy => hy.2) ?_
  intro a u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hu, hv, hw, sub_self, mul_zero, zero_add]

theorem positive_mem_intrinsicInterior {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    x ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι)) := by
  let p : affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι)) :=
    ⟨x, subset_affineSpan ℝ simplex hx⟩
  refine mem_intrinsicInterior.mpr ⟨p, ?_, rfl⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hevent : ∀ᶠ y : affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι)) in 𝓝 p,
      ∀ i, 0 < (y : EuclideanSpace ℝ ι) i := by
    rw [Filter.eventually_all]
    intro i
    exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).comp continuous_subtype_val).continuousAt
      (Ioi_mem_nhds (hpos i))
  filter_upwards [hevent] with y hy
  exact ⟨fun i => (hy i).le, sum_eq_one_of_mem_affineSpan y.property⟩

theorem positive_of_mem_intrinsicInterior {x : EuclideanSpace ℝ ι}
    (hx : x ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι))) :
    ∀ i, 0 < x i := by
  classical
  intro i
  have hxmem := intrinsicInterior_subset hx
  by_contra h
  have hzero : x i = 0 := le_antisymm (not_lt.mp h) (hxmem.1 i)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (Pi.single i 1)
  have hv : v ∈ simplex := single_mem_stdSimplex ℝ i
  have hevent := Duality.eventually_lineMap_mem hx hv
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have ht : dist (-ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -ε / 2 < 0)]
    linarith
  have hnonneg := (hball ht).1 i
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, hzero, sub_zero, add_zero] at hnonneg
  have hvi : v i = 1 := by simp [v]
  rw [hvi, mul_one] at hnonneg
  linarith

theorem mem_intrinsicInterior_iff {x : EuclideanSpace ℝ ι} :
    x ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι)) ↔
      x ∈ simplex ∧ ∀ i, 0 < x i :=
  ⟨fun hx => ⟨intrinsicInterior_subset hx, positive_of_mem_intrinsicInterior hx⟩,
    fun hx => positive_mem_intrinsicInterior hx.1 hx.2⟩

theorem differentiableWithinAt_entropy {x : EuclideanSpace ℝ ι}
    (hx : x ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι))) :
    DifferentiableWithinAt ℝ entropy simplex x :=
  (entropy_hasFDerivAt (positive_of_mem_intrinsicInterior hx)).differentiableAt.differentiableWithinAt

theorem contDiffOn_entropy_intrinsicInterior :
    ContDiffOn ℝ ∞ (entropy : EuclideanSpace ℝ ι → ℝ) (intrinsicInterior ℝ simplex) :=
  fun _ hx => (contDiffAt_entropy (positive_of_mem_intrinsicInterior hx)).contDiffWithinAt

/-- A coordinate difference of the entropy gradient is controlled by its
canonical relative gradient; normal components play no role. -/
theorem log_sub_log_le_relativeGradient {x : EuclideanSpace ℝ ι}
    (hx : x ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι))) (i j : ι) :
    |Real.log (x i) - Real.log (x j)| ≤
      2 * ‖relativeGradient simplex entropy x‖ := by
  classical
  let ei : EuclideanSpace ℝ ι := PiLp.single 2 i 1
  let ej : EuclideanSpace ℝ ι := PiLp.single 2 j 1
  have hei : ei ∈ simplex := single_mem_stdSimplex ℝ i
  have hej : ej ∈ simplex := single_mem_stdSimplex ℝ j
  let v : (affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))).direction :=
    ⟨ei - ej, AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ simplex hei) (subset_affineSpan ℝ simplex hej)⟩
  have hvnorm : ‖v‖ ≤ 2 := by
    change ‖ei - ej‖ ≤ 2
    calc
      ‖ei - ej‖ ≤ ‖ei‖ + ‖ej‖ := norm_sub_le _ _
      _ = 2 := by norm_num [ei, ej]
  let g := (fderivWithin ℝ entropy simplex x).comp
    (affineSpan ℝ (simplex : Set (EuclideanSpace ℝ ι))).direction.subtypeL
  have hgv : g v = Real.log (x i) - Real.log (x j) := by
    dsimp only [g]
    rw [restricted_fderivWithin_eq hx
      (entropy_hasFDerivAt (positive_of_mem_intrinsicInterior hx)).hasFDerivWithinAt]
    simp [v, ei, ej, innerSL_apply_apply, inner_sub_right,
      EuclideanSpace.inner_single_right, entropyGradient]
  calc
    |Real.log (x i) - Real.log (x j)| = ‖g v‖ := by rw [hgv, Real.norm_eq_abs]
    _ ≤ ‖g‖ * ‖v‖ := g.le_opNorm v
    _ ≤ ‖g‖ * 2 := mul_le_mul_of_nonneg_left hvnorm (norm_nonneg g)
    _ = 2 * ‖relativeGradient simplex entropy x‖ := by
      rw [norm_relativeGradient]
      exact mul_comm _ _

theorem gradientBlowsUpAtBoundary_entropy :
    LegendreBoundary.GradientBlowsUpAtBoundary simplex (entropy : EuclideanSpace ℝ ι → ℝ) := by
  classical
  intro x hx hboundary z hz hzx
  have hxmem : x ∈ simplex := isCompact_simplex.isClosed.closure_subset hx
  have hi : ∃ i, x i = 0 := by
    by_contra h
    push Not at h
    exact hboundary (positive_mem_intrinsicInterior hxmem
      (fun i => lt_of_le_of_ne (hxmem.1 i) (Ne.symm (h i))))
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, 0 < x j := by
    by_contra h
    push Not at h
    have hs := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => h j)
    rw [hxmem.2] at hs
    norm_num at hs
  obtain ⟨j, hj⟩ := hj
  have hzi : Tendsto (fun n => z n i) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => positive_of_mem_intrinsicInterior (hz n) i)⟩
    simpa only [EuclideanSpace.coe_proj, Function.comp_def, hi] using
      (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous).continuousAt.tendsto.comp hzx)
  have hlogi : Tendsto (fun n => Real.log (z n i)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hzi
  have hlogj : Tendsto (fun n => Real.log (z n j)) atTop (𝓝 (Real.log (x j))) :=
    (Real.continuousAt_log hj.ne').tendsto.comp
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous).continuousAt.tendsto.comp hzx)
  apply tendsto_atTop.mpr
  intro r
  have hile : ∀ᶠ n in atTop, Real.log (z n i) ≤ Real.log (x j) - 1 - 2 * r :=
    (tendsto_atBot.mp hlogi) _
  have hjge : ∀ᶠ n in atTop, Real.log (x j) - 1 < Real.log (z n j) :=
    hlogj (Ioi_mem_nhds (by linarith))
  filter_upwards [hile, hjge] with n hin hjn
  have hb := log_sub_log_le_relativeGradient (hz n) i j
  have habs := neg_le_abs (Real.log (z n i) - Real.log (z n j))
  linarith

theorem sum_exp_pos [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    0 < ∑ i, Real.exp (u i) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (u i)) Finset.univ_nonempty

theorem softmax_pos [Nonempty ι] (u : EuclideanSpace ℝ ι) (i : ι) :
    0 < softmax u i := div_pos (Real.exp_pos _) (sum_exp_pos u)

theorem softmax_mem_simplex [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    softmax u ∈ simplex := by
  refine ⟨fun i => (softmax_pos u i).le, ?_⟩
  simp only [softmax_apply, ← Finset.sum_div]
  exact div_self (sum_exp_pos u).ne'

theorem softmax_mem_intrinsicInterior [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    softmax u ∈ intrinsicInterior ℝ (simplex : Set (EuclideanSpace ℝ ι)) :=
  positive_mem_intrinsicInterior (softmax_mem_simplex u) (softmax_pos u)

theorem uniform_mem_simplex [Nonempty ι] :
    (uniform : EuclideanSpace ℝ ι) ∈ simplex := by
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
  simp [uniform, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

theorem log_softmax [Nonempty ι] (u : EuclideanSpace ℝ ι) (i : ι) :
    Real.log (softmax u i) = u i - logSumExp u := by
  rw [softmax_apply, Real.log_div (Real.exp_ne_zero _) (sum_exp_pos u).ne', Real.log_exp]
  rfl

/-- The scalar entropy inequality, valid also when the comparator is zero. -/
theorem sub_le_mul_log_sub {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    x - p ≤ x * Real.log x - x * Real.log p := by
  by_cases hx0 : x = 0
  · simp only [hx0, zero_mul, sub_zero, zero_sub]
    exact neg_nonpos.mpr hp.le
  calc
    x - p = p * (x / p - 1) := by field_simp
    _ ≤ p * ((x / p) * Real.log (x / p)) :=
      mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log (div_nonneg hx hp.le)) hp.le
    _ = x * Real.log x - x * Real.log p := by
      rw [Real.log_div hx0 hp.ne']
      field_simp

theorem conjugate_objective_le [Nonempty ι] (u : EuclideanSpace ℝ ι)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ simplex) :
    ⟪u, x⟫_ℝ - entropy x ≤ logSumExp u := by
  have h (i : ι) : u i * x i - x i * Real.log (x i) ≤
      logSumExp u * x i + softmax u i - x i := by
    have hs := sub_le_mul_log_sub (hx.1 i) (softmax_pos u i)
    rw [log_softmax] at hs
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa only [PiLp.inner_apply, Real.inner_apply, entropy, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, (softmax_mem_simplex u).2,
    mul_one, add_sub_cancel_right] using hs

theorem conjugate_objective_softmax [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    ⟪u, softmax u⟫_ℝ - entropy (softmax u) = logSumExp u := by
  simp only [PiLp.inner_apply, Real.inner_apply, entropy, log_softmax,
    ← Finset.sum_sub_distrib]
  calc
    ∑ i, (u i * softmax u i - softmax u i * (u i - logSumExp u)) =
        ∑ i, logSumExp u * softmax u i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = logSumExp u := by rw [← Finset.mul_sum, (softmax_mem_simplex u).2, mul_one]

theorem mem_dualDomain [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    u ∈ Duality.dualDomain simplex entropy := by
  refine ⟨logSumExp u, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact conjugate_objective_le u hx

theorem conjugate_eq_logSumExp [Nonempty ι] :
    Duality.conjugate simplex (entropy : EuclideanSpace ℝ ι → ℝ) = logSumExp := by
  funext u
  apply le_antisymm
  · exact Duality.conjugate_le ⟨softmax u, softmax_mem_simplex u⟩
      (fun _ hx => conjugate_objective_le u hx)
  · rw [← conjugate_objective_softmax u]
    exact Duality.le_conjugate (mem_dualDomain u) (softmax_mem_simplex u)

theorem logSumExp_hasFDerivAt [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    HasFDerivAt logSumExp (innerSL ℝ (softmax u)) u := by
  have hs : HasFDerivAt (fun v : EuclideanSpace ℝ ι => ∑ i, Real.exp (v i))
      (∑ i, Real.exp (u i) • EuclideanSpace.proj (𝕜 := ℝ) i) u := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hp : HasFDerivAt (fun v : EuclideanSpace ℝ ι => v i)
        (EuclideanSpace.proj (𝕜 := ℝ) i) u :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    exact hp.exp
  convert! hs.log (sum_exp_pos u).ne' using 1
  ext v
  simp [innerSL_apply_apply, PiLp.inner_apply, softmax,
    div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem gradient_logSumExp [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    gradient logSumExp u = softmax u := by
  have h : HasGradientAt logSumExp (softmax u) u := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact logSumExp_hasFDerivAt u
  exact h.gradient

theorem gradient_conjugate [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    gradient (Duality.conjugate simplex entropy) u = softmax u := by
  rw [conjugate_eq_logSumExp]
  exact gradient_logSumExp u

end AltOMD.Shannon
