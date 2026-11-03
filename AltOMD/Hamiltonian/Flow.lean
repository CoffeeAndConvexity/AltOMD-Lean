import AltOMD.Hamiltonian.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Taylor expansion along actual ODE trajectories

Lie derivatives are defined by the actual Fréchet derivative. The ODE equation
and the chain rule identify their iterates with time derivatives; the scalar
Taylor theorem then supplies the factorial remainder estimate. The explicit
separable shear flows are checked directly.
-/

open scoped ContDiff
open Set Finset

namespace AltOMD.Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiation of an observable along a vector field. -/
noncomputable def lie (V : E → E) (f : E → ℝ) (z : E) : ℝ :=
  fderiv ℝ f z (V z)

noncomputable def lieIterate (V : E → E) (f : E → ℝ) : ℕ → E → ℝ
  | 0 => f
  | k + 1 => lie V (lieIterate V f k)

theorem contDiff_lie {V : E → E} {f : E → ℝ}
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (lie V f) :=
  (hf.fderiv_right (by simp)).clm_apply hV

theorem contDiff_lieIterate {V : E → E} {f : E → ℝ}
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (lieIterate V f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact contDiff_lie hV ih

/-- The chain rule along an actual solution of the ODE. -/
theorem hasDerivAt_comp_trajectory {V : E → E} {f : E → ℝ} {φ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (φ t)) (hφ : HasDerivAt φ (V (φ t)) t) :
    HasDerivAt (f ∘ φ) (lie V f (φ t)) t :=
  hf.hasFDerivAt.comp_hasDerivAt t hφ

/-- Repeated time differentiation equals repeated Lie differentiation. -/
theorem iteratedDeriv_comp_trajectory {V : E → E} {f : E → ℝ} {φ : ℝ → E}
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hφ : ∀ t, HasDerivAt φ (V (φ t)) t) (k : ℕ) :
    iteratedDeriv k (f ∘ φ) = fun t => lieIterate V f k (φ t) := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hasDerivAt_comp_trajectory
        ((contDiff_lieIterate hV hf k).differentiable (by simp) (φ t)) (hφ t)).deriv

/-- Taylor's factorial bound for the actual flow, with Lie coefficients. -/
theorem flow_taylor_remainder {V : E → E} {f : E → ℝ} {φ : ℝ → E}
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hφsmooth : ContDiff ℝ ∞ φ)
    (hφ : ∀ t, HasDerivAt φ (V (φ t)) t)
    (m : ℕ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ t ∈ Icc 0 h, |lieIterate V f (m + 1) (φ t)| ≤ M) :
    |f (φ h) - ∑ k ∈ range (m + 1),
      h ^ k / (k.factorial : ℝ) * lieIterate V f k (φ 0)| ≤
        M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hbound := AltOMD.taylor_remainder_bound (f ∘ φ) (hf.comp hφsmooth) m hh
    (fun t ht => by
      rw [iteratedDeriv_comp_trajectory hV hf hφ]
      exact hM t ht)
  simpa only [AltOMD.taylorPolynomial,
    iteratedDeriv_comp_trajectory hV hf hφ, Function.comp_apply] using hbound

/-- Propagating the errors of the second expansion through the first one. -/
theorem weighted_expansion_error (s : Finset ℕ) (w b c R : ℕ → ℝ) (a RF : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k)
    (hF : |a - ∑ k ∈ s, w k * b k| ≤ RF)
    (hG : ∀ k ∈ s, |b k - c k| ≤ R k) :
    |a - ∑ k ∈ s, w k * c k| ≤ RF + ∑ k ∈ s, w k * R k := by
  have heq : a - ∑ k ∈ s, w k * c k =
      (a - ∑ k ∈ s, w k * b k) + ∑ k ∈ s, w k * (b k - c k) := by
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add hF
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k hk
  rw [abs_mul, abs_of_nonneg (hw k hk)]
  exact mul_le_mul_of_nonneg_left (hG k hk) (hw k hk)

/-- Ordered triangular Lie polynomial for first flowing along `VG`, then `VF`.
The coefficient is `L_G^α L_F^β f`, in that order. -/
noncomputable def triangularTaylor (VF VG : E → E) (f : E → ℝ)
    (m : ℕ) (h : ℝ) (z : E) : ℝ :=
  ∑ β ∈ range (m + 1), h ^ β / (β.factorial : ℝ) *
    ∑ α ∈ range (m - β + 1), h ^ α / (α.factorial : ℝ) *
      lieIterate VG (lieIterate VF f β) α z

/-- Sequential real Taylor expansion along two actual flows. The scalar sum on
the right simplifies to the binomial factor `2^(m+1)`. -/
theorem two_flow_remainder_sum {VF VG : E → E} {f : E → ℝ}
    (hVF : ContDiff ℝ ∞ VF) (hVG : ContDiff ℝ ∞ VG) (hf : ContDiff ℝ ∞ f)
    (φF φG : ℝ → E → E)
    (hFsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φF t z))
    (hGsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φG t z))
    (hFode : ∀ z t, HasDerivAt (fun s => φF s z) (VF (φF t z)) t)
    (hGode : ∀ z t, HasDerivAt (fun s => φG s z) (VG (φG t z)) t)
    (hFzero : ∀ z, φF 0 z = z) (hGzero : ∀ z, φG 0 z = z)
    (m : ℕ) (z : E) {h M : ℝ} (hh : 0 ≤ h)
    (hMF : ∀ t ∈ Icc 0 h,
      |lieIterate VF f (m + 1) (φF t (φG h z))| ≤ M)
    (hMG : ∀ β ≤ m, ∀ t ∈ Icc 0 h,
      |lieIterate VG (lieIterate VF f β) (m - β + 1) (φG t z)| ≤ M) :
    |f (φF h (φG h z)) - triangularTaylor VF VG f m h z| ≤
      M * h ^ (m + 1) / ((m + 1).factorial : ℝ) +
        ∑ β ∈ range (m + 1), (h ^ β / (β.factorial : ℝ)) *
          (M * h ^ (m - β + 1) / ((m - β + 1).factorial : ℝ)) := by
  have hF := flow_taylor_remainder hVF hf (hFsmooth (φG h z))
    (hFode (φG h z)) m hh hMF
  simp only [hFzero] at hF
  have hG (β : ℕ) (hβ : β ∈ range (m + 1)) :
      |lieIterate VF f β (φG h z) -
        ∑ α ∈ range (m - β + 1), h ^ α / (α.factorial : ℝ) *
          lieIterate VG (lieIterate VF f β) α z| ≤
        M * h ^ (m - β + 1) / ((m - β + 1).factorial : ℝ) := by
    have hb := flow_taylor_remainder hVG (contDiff_lieIterate hVF hf β)
      (hGsmooth z) (hGode z) (m - β) hh
      (hMG β (Nat.le_of_lt_succ (mem_range.mp hβ)))
    simpa only [hGzero] using hb
  exact weighted_expansion_error (range (m + 1))
    (fun β => h ^ β / (β.factorial : ℝ))
    (fun β => lieIterate VF f β (φG h z))
    (fun β => ∑ α ∈ range (m - β + 1), h ^ α / (α.factorial : ℝ) *
      lieIterate VG (lieIterate VF f β) α z)
    (fun β => M * h ^ (m - β + 1) / ((m - β + 1).factorial : ℝ))
    (f (φF h (φG h z))) (M * h ^ (m + 1) / ((m + 1).factorial : ℝ))
    (fun β _ => div_nonneg (pow_nonneg hh _) (Nat.cast_nonneg _)) hF hG

/-- The composed-flow remainder with the manuscript's exact binomial constant. -/
theorem two_flow_remainder {VF VG : E → E} {f : E → ℝ}
    (hVF : ContDiff ℝ ∞ VF) (hVG : ContDiff ℝ ∞ VG) (hf : ContDiff ℝ ∞ f)
    (φF φG : ℝ → E → E)
    (hFsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φF t z))
    (hGsmooth : ∀ z, ContDiff ℝ ∞ (fun t => φG t z))
    (hFode : ∀ z t, HasDerivAt (fun s => φF s z) (VF (φF t z)) t)
    (hGode : ∀ z t, HasDerivAt (fun s => φG s z) (VG (φG t z)) t)
    (hFzero : ∀ z, φF 0 z = z) (hGzero : ∀ z, φG 0 z = z)
    (m : ℕ) (z : E) {h M : ℝ} (hh : 0 ≤ h)
    (hMF : ∀ t ∈ Icc 0 h,
      |lieIterate VF f (m + 1) (φF t (φG h z))| ≤ M)
    (hMG : ∀ β ≤ m, ∀ t ∈ Icc 0 h,
      |lieIterate VG (lieIterate VF f β) (m - β + 1) (φG t z)| ≤ M) :
    |f (φF h (φG h z)) - triangularTaylor VF VG f m h z| ≤
      (2 : ℝ) ^ (m + 1) * M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hb := two_flow_remainder_sum hVF hVG hf φF φG hFsmooth hGsmooth
    hFode hGode hFzero hGzero m z hh hMF hMG
  rw [AltOMD.split_taylor_weight] at hb
  exact hb

section Shears

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The flow that fixes the first coordinate. -/
def shearF (v : E → F) (t : ℝ) (z : E × F) : E × F :=
  (z.1, z.2 + t • v z.1)

def fieldF (v : E → F) (z : E × F) : E × F := (0, v z.1)

/-- The flow that fixes the second coordinate; the minus sign is included in `v`. -/
def shearG (v : F → E) (t : ℝ) (z : E × F) : E × F :=
  (z.1 + t • v z.2, z.2)

def fieldG (v : F → E) (z : E × F) : E × F := (v z.2, 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem shearF_zero (v : E → F) (z : E × F) : shearF v 0 z = z := by
  simp [shearF]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp] theorem shearG_zero (v : F → E) (z : E × F) : shearG v 0 z = z := by
  simp [shearG]

theorem hasDerivAt_shearF (v : E → F) (z : E × F) (t : ℝ) :
    HasDerivAt (fun s => shearF v s z) (fieldF v (shearF v t z)) t := by
  simpa [shearF, fieldF] using
    (hasDerivAt_const t z.1).prodMk
      ((hasDerivAt_id t).smul_const (v z.1) |>.const_add z.2)

theorem hasDerivAt_shearG (v : F → E) (z : E × F) (t : ℝ) :
    HasDerivAt (fun s => shearG v s z) (fieldG v (shearG v t z)) t := by
  simpa [shearG, fieldG] using
    ((hasDerivAt_id t).smul_const (v z.2) |>.const_add z.1).prodMk
      (hasDerivAt_const t z.2)

theorem contDiff_shearF (v : E → F) (z : E × F) :
    ContDiff ℝ ∞ (fun t => shearF v t z) :=
  contDiff_const.prodMk (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem contDiff_shearG (v : F → E) (z : E × F) :
    ContDiff ℝ ∞ (fun t => shearG v t z) :=
  (contDiff_const.add (contDiff_id.smul contDiff_const)).prodMk contDiff_const

end Shears

end AltOMD.Flow
