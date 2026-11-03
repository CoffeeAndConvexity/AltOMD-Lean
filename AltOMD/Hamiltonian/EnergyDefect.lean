import AltOMD.Hamiltonian.Flow
import AltOMD.Hamiltonian.ModifiedEnergy
import AltOMD.Hamiltonian.FormalEnergy
import AltOMD.Hamiltonian.PoissonFlow
import Mathlib.Algebra.BigOperators.Intervals

/-!
# From formal cancellation to the real modified-energy defect

All rearrangements below are finite. The real flow remainder is supplied by
`Flow.two_flow_remainder`; the polynomial part vanishes by the positive-degree
coefficient identities of formal BCH preservation.
-/

open scoped ContDiff
open Finset Set

namespace AltOMD.EnergyDefect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The total-degree coefficient of the ordered split-flow expansion. -/
noncomputable def splitCoefficient (VF VG : E → E) (f : E → ℝ)
    (q : ℕ) (z : E) : ℝ :=
  ∑ β ∈ range (q + 1),
    Flow.lieIterate VG (Flow.lieIterate VF f β) (q - β) z /
      (((q - β).factorial : ℝ) * (β.factorial : ℝ))

@[simp] theorem splitCoefficient_zero (VF VG : E → E) (f : E → ℝ) (z : E) :
    splitCoefficient VF VG f 0 z = f z := by
  simp [splitCoefficient, Flow.lieIterate]

/-- Collecting the triangular polynomial by total degree preserves operator order. -/
theorem triangularTaylor_eq_degree_sum (VF VG : E → E) (f : E → ℝ)
    (m : ℕ) (h : ℝ) (z : E) :
    Flow.triangularTaylor VF VG f m h z =
      ∑ q ∈ range (m + 1), h ^ q * splitCoefficient VF VG f q z := by
  calc
    _ = ∑ β ∈ range (m + 1), ∑ α ∈ range (m + 1 - β),
        h ^ β / (β.factorial : ℝ) *
          (h ^ α / (α.factorial : ℝ) *
            Flow.lieIterate VG (Flow.lieIterate VF f β) α z) := by
      unfold Flow.triangularTaylor
      apply sum_congr rfl
      intro β hβ
      rw [show m - β + 1 = m + 1 - β by have := mem_range.mp hβ; omega,
        mul_sum]
    _ = ∑ q ∈ range (m + 1), ∑ β ∈ range (q + 1),
        h ^ β / (β.factorial : ℝ) *
          (h ^ (q - β) / ((q - β).factorial : ℝ) *
            Flow.lieIterate VG (Flow.lieIterate VF f β) (q - β) z) :=
      (sum_range_diag_flip (m + 1) _).symm
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      unfold splitCoefficient
      rw [mul_sum]
      apply sum_congr rfl
      intro β hβ
      have hp : h ^ q = h ^ β * h ^ (q - β) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hβ))]
      rw [hp]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The range form agrees with the antidiagonal coefficients of formal BCH. -/
theorem splitCoefficient_eq_antidiagonal (VF VG : E → E) (f : E → ℝ)
    (q : ℕ) (z : E) :
    splitCoefficient VF VG f q z =
      ∑ p ∈ antidiagonal q,
        Flow.lieIterate VG (Flow.lieIterate VF f p.2) p.1 z /
          ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The scalar coefficient identities used below are obtained by evaluating
the proved formal preservation theorem for actual smooth Hamiltonians. -/
theorem corrected_scalar_cancellation
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : AltOMD.IsSkewPoissonTensor J)
    (G F : AltOMD.SmoothScalar E) (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (AltOMD.SmoothScalar E))
    (j : ℕ) (z : E) :
    (∑ r ∈ range j,
      splitCoefficient (AltOMD.hamiltonianField J F) (AltOMD.hamiltonianField J G)
        ((FormalEnergy.correctedHamiltonian (AltOMD.smoothPoissonBracket J) G F Z r :
          AltOMD.SmoothScalar E) : E → ℝ)
        (j - r) z) = 0 := by
  let ev : AltOMD.SmoothScalar E →ₗ[ℝ] ℝ :=
    { toFun := fun f => (f : E → ℝ) z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc := FormalEnergy.correctedHamiltonian_cancellation
    (AltOMD.smoothPoissonBracket J) (AltOMD.smoothPoissonBracket_antisymm J hJ)
    (AltOMD.poissonGenerator_bracket J hJ) G F Z bch j
  have he := congrArg ev hc
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
  have hev (f : AltOMD.SmoothScalar E) : ev f = (f : E → ℝ) z := rfl
  simp only [hev] at he
  simpa only [splitCoefficient_eq_antidiagonal,
    AltOMD.mixed_lieIterate_hamiltonianField, AltOMD.poissonGenerator,
    div_eq_mul_inv, one_mul, mul_one, mul_comm] using he

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The finite modified energy is the sum of its coefficients through order `N`. -/
theorem truncatedEnergy_eq_sum (H : ℕ → E → ℝ) (N : ℕ) (h : ℝ) (z : E) :
    AltOMD.truncatedEnergy H N h z = ∑ r ∈ range (N + 1), h ^ r * H r z := by
  rw [sum_range_succ']
  simp only [pow_zero, one_mul]
  unfold AltOMD.truncatedEnergy
  ring

/-- Positive-degree formal cancellation annihilates the complete finite
polynomial left by the weighted Taylor expansions. -/
theorem weighted_triangular_cancellation (VF VG : E → E) (H : ℕ → E → ℝ)
    (N : ℕ) (h : ℝ) (z : E)
    (hcancel : ∀ j ∈ range (N + 1),
      ∑ r ∈ range (j + 1), splitCoefficient VF VG (H r) (j + 1 - r) z = 0) :
    (∑ r ∈ range (N + 1), h ^ r *
      (Flow.triangularTaylor VF VG (H r) (N + 1 - r) h z - H r z)) = 0 := by
  have hsub (r : ℕ) :
      Flow.triangularTaylor VF VG (H r) (N + 1 - r) h z - H r z =
        ∑ q ∈ range (N + 1 - r),
          h ^ (q + 1) * splitCoefficient VF VG (H r) (q + 1) z := by
    rw [triangularTaylor_eq_degree_sum, sum_range_succ']
    simp only [pow_zero, one_mul, splitCoefficient_zero, add_sub_cancel_right]
  simp_rw [hsub, mul_sum]
  have hterm (r q : ℕ) :
      h ^ r * (h ^ (q + 1) * splitCoefficient VF VG (H r) (q + 1) z) =
        h ^ (r + q + 1) * splitCoefficient VF VG (H r) (q + 1) z := by
    rw [show r + q + 1 = r + (q + 1) by omega, pow_add]
    ring
  simp_rw [hterm]
  rw [← sum_range_diag_flip]
  apply sum_eq_zero
  intro j hj
  have hrow : (∑ r ∈ range (j + 1), h ^ (r + (j - r) + 1) *
      splitCoefficient VF VG (H r) (j - r + 1) z) =
        h ^ (j + 1) * ∑ r ∈ range (j + 1),
          splitCoefficient VF VG (H r) (j + 1 - r) z := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hrj : r ≤ j := Nat.le_of_lt_succ (mem_range.mp hr)
    rw [show r + (j - r) + 1 = j + 1 by omega,
      show j - r + 1 = j + 1 - r by omega]
  rw [hrow, hcancel j hj, mul_zero]

/-- Only the actual real remainders remain after the finite polynomial cancels. -/
theorem defect_le_sum_remainders (VF VG : E → E) (H : ℕ → E → ℝ)
    (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (z znext : E) (R : ℕ → ℝ)
    (hcancel : ∀ j ∈ range (N + 1),
      ∑ r ∈ range (j + 1), splitCoefficient VF VG (H r) (j + 1 - r) z = 0)
    (hrem : ∀ r ∈ range (N + 1),
      |H r znext - Flow.triangularTaylor VF VG (H r) (N + 1 - r) h z| ≤ R r) :
    |AltOMD.truncatedEnergy H N h znext - AltOMD.truncatedEnergy H N h z| ≤
      ∑ r ∈ range (N + 1), h ^ r * R r := by
  have hc := weighted_triangular_cancellation VF VG H N h z hcancel
  have heq : AltOMD.truncatedEnergy H N h znext - AltOMD.truncatedEnergy H N h z =
      ∑ r ∈ range (N + 1), h ^ r *
        (H r znext - Flow.triangularTaylor VF VG (H r) (N + 1 - r) h z) := by
    rw [truncatedEnergy_eq_sum, truncatedEnergy_eq_sum]
    simp only [mul_sub, sum_sub_distrib] at hc ⊢
    linarith
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r hr
  rw [abs_mul, abs_of_nonneg (pow_nonneg hh r)]
  exact mul_le_mul_of_nonneg_left (hrem r hr) (pow_nonneg hh r)

/-- Actual flow Taylor bounds and coefficient cancellation imply the energy
defect, uniformly from one bound on all required mixed Lie derivatives. -/
theorem defect_bound_from_mixed_lie {VF VG : E → E} (H : ℕ → E → ℝ)
    (hVF : ContDiff ℝ ∞ VF) (hVG : ContDiff ℝ ∞ VG)
    (φF φG : ℝ → E → E)
    (hFsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φF t z))
    (hGsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φG t z))
    (hFode : ∀ z t, HasDerivAt (fun s => φF s z) (VF (φF t z)) t)
    (hGode : ∀ z t, HasDerivAt (fun s => φG s z) (VG (φG t z)) t)
    (hFzero : ∀ z, φF 0 z = z) (hGzero : ∀ z, φG 0 z = z)
    (N : ℕ) (hH : ∀ r ≤ N, ContDiff ℝ ∞ (H r))
    {h M : ℝ} (hh : 0 ≤ h) (hM : 0 ≤ M) (z : E)
    (hcancel : ∀ j ∈ range (N + 1),
      ∑ r ∈ range (j + 1), splitCoefficient VF VG (H r) (j + 1 - r) z = 0)
    (hLie : ∀ r ≤ N, ∀ α β, r + α + β = N + 2 → ∀ w,
      |Flow.lieIterate VG (Flow.lieIterate VF (H r) β) α w| ≤ M) :
    |AltOMD.truncatedEnergy H N h (φF h (φG h z)) -
      AltOMD.truncatedEnergy H N h z| ≤ Real.exp 2 * h ^ (N + 2) * M := by
  have hrem (r : ℕ) (hr : r ∈ range (N + 1)) :
      |H r (φF h (φG h z)) -
        Flow.triangularTaylor VF VG (H r) (N + 1 - r) h z| ≤
          (2 : ℝ) ^ (N + 2 - r) * M * h ^ (N + 2 - r) /
            ((N + 2 - r).factorial : ℝ) := by
    have hrN : r ≤ N := Nat.le_of_lt_succ (mem_range.mp hr)
    have hb := Flow.two_flow_remainder hVF hVG (hH r hrN) φF φG
      hFsmooth hGsmooth hFode hGode hFzero hGzero (N + 1 - r) z hh
      (fun t _ => by
        simpa only [Flow.lieIterate] using
          hLie r hrN 0 (N + 1 - r + 1) (by omega) (φF t (φG h z)))
      (fun β hβ t _ => hLie r hrN (N + 1 - r - β + 1) β (by omega) (φG t z))
    simpa only [show N + 1 - r + 1 = N + 2 - r by omega] using hb
  have hb := defect_le_sum_remainders VF VG H N hh z (φF h (φG h z))
    (fun r => (2 : ℝ) ^ (N + 2 - r) * M * h ^ (N + 2 - r) /
      ((N + 2 - r).factorial : ℝ)) hcancel hrem
  apply hb.trans
  calc
    _ = (M * h ^ (N + 2)) * ∑ r ∈ range (N + 1),
        (2 : ℝ) ^ (N + 2 - r) / ((N + 2 - r).factorial : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      have hp : h ^ (N + 2) = h ^ r * h ^ (N + 2 - r) := by
        rw [← pow_add, Nat.add_sub_of_le (by have := mem_range.mp hr; omega)]
      rw [hp]
      ring
    _ ≤ (M * h ^ (N + 2)) * Real.exp 2 :=
      mul_le_mul_of_nonneg_left (AltOMD.remainder_weight_sum_le_exp N)
        (mul_nonneg hM (pow_nonneg hh _))
    _ = _ := by ring

/-- The factorial defect estimate, with the constants of the manuscript. -/
theorem factorial_defect_from_mixed_lie {VF VG : E → E} (H : ℕ → E → ℝ)
    (hVF : ContDiff ℝ ∞ VF) (hVG : ContDiff ℝ ∞ VG)
    (φF φG : ℝ → E → E)
    (hFsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φF t z))
    (hGsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φG t z))
    (hFode : ∀ z t, HasDerivAt (fun s => φF s z) (VF (φF t z)) t)
    (hGode : ∀ z t, HasDerivAt (fun s => φG s z) (VG (φG t z)) t)
    (hFzero : ∀ z, φF 0 z = z) (hGzero : ∀ z, φG 0 z = z)
    (N : ℕ) (hH : ∀ r ≤ N, ContDiff ℝ ∞ (H r))
    {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C) (z : E)
    (hcancel : ∀ j ∈ range (N + 1),
      ∑ r ∈ range (j + 1), splitCoefficient VF VG (H r) (j + 1 - r) z = 0)
    (hLie : ∀ r ≤ N, ∀ α β, 0 < r + α + β → ∀ w,
      |Flow.lieIterate VG (Flow.lieIterate VF (H r) β) α w| ≤
        (4 * C) ^ (r + α + β + 1) * ((r + α + β).factorial : ℝ)) :
    |AltOMD.truncatedEnergy H N h (φF h (φG h z)) -
      AltOMD.truncatedEnergy H N h z| ≤
        Real.exp 2 * h ^ (N + 2) * (4 * C) ^ (N + 3) * ((N + 2).factorial : ℝ) := by
  have hb := defect_bound_from_mixed_lie H hVF hVG φF φG hFsmooth hGsmooth
    hFode hGode hFzero hGzero N hH hh
    (show 0 ≤ (4 * C) ^ (N + 3) * ((N + 2).factorial : ℝ) by positivity) z hcancel
    (fun r hr α β hd w => by
      have hbound := hLie r hr α β (by omega) w
      simpa only [hd, Nat.add_assoc] using hbound)
  simpa only [mul_assoc] using hb

end AltOMD.EnergyDefect
