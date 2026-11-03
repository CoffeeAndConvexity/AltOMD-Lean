import AltOMD.Hamiltonian.Poisson
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The game operator as a constant Poisson tensor

The product uses Lean's standard maximum norm. The tensor still has operator
norm at most `‖A‖`, because restriction of a covector to either coordinate has
norm at most one. Its two separable Hamiltonian fields are exactly the shear
fields used to define the alternating update.
-/

noncomputable section

namespace AltOMD.CoupledTensor

open scoped InnerProductSpace ContDiff BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ F := InnerProductSpace.toNormedSpace

def riesz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (E →L[ℝ] ℝ) →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem riesz_norm (b : E →L[ℝ] ℝ) : ‖riesz E b‖ = ‖b‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map b

@[simp] theorem riesz_pairing (b : E →L[ℝ] ℝ) (x : E) :
    inner ℝ (riesz E b) x = b x := InnerProductSpace.toDual_symm_apply

def firstRestriction : ((E × F) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E (E × F) ℝ).flip (ContinuousLinearMap.inl ℝ E F)

def secondRestriction : ((E × F) →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ F (E × F) ℝ).flip (ContinuousLinearMap.inr ℝ E F)

@[simp] theorem firstRestriction_apply (b : (E × F) →L[ℝ] ℝ) (x : E) :
    firstRestriction b x = b (x, 0) := rfl

@[simp] theorem secondRestriction_apply (b : (E × F) →L[ℝ] ℝ) (y : F) :
    secondRestriction b y = b (0, y) := rfl

theorem firstRestriction_norm_le (b : (E × F) →L[ℝ] ℝ) : ‖firstRestriction b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (firstRestriction b) (norm_nonneg b)
  intro x
  simpa using b.le_opNorm (x, (0 : F))

theorem secondRestriction_norm_le (b : (E × F) →L[ℝ] ℝ) : ‖secondRestriction b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (secondRestriction b) (norm_nonneg b)
  intro y
  simpa using b.le_opNorm ((0 : E), y)

theorem pairing_decompose (b : (E × F) →L[ℝ] ℝ) (z : E × F) :
    b z = firstRestriction b z.1 + secondRestriction b z.2 := by
  change b z = b (z.1, 0) + b (0, z.2)
  rw [← map_add]
  congr 1
  ext <;> simp

def tensor (A : E →L[ℝ] F) : ((E × F) →L[ℝ] ℝ) →L[ℝ] E × F :=
  ((-A.adjoint).comp ((riesz F).comp secondRestriction)).prod
    (A.comp ((riesz E).comp firstRestriction))

@[simp] theorem tensor_apply (A : E →L[ℝ] F) (b : (E × F) →L[ℝ] ℝ) :
    tensor A b = (-A.adjoint (riesz F (secondRestriction b)),
      A (riesz E (firstRestriction b))) := rfl

theorem tensor_norm_le (A : E →L[ℝ] F) :
    ‖(tensor (E := E) (F := F) A : ((E × F) →L[ℝ] ℝ) →L[ℝ] (E × F))‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (tensor A) (norm_nonneg A)
  intro b
  rw [tensor_apply, Prod.norm_def, norm_neg]
  apply max_le
  · calc
      ‖A.adjoint (riesz F (secondRestriction b))‖ ≤
          ‖A.adjoint‖ * ‖riesz F (secondRestriction b)‖ := A.adjoint.le_opNorm _
      _ = ‖A‖ * ‖secondRestriction b‖ := by simp
      _ ≤ ‖A‖ * ‖b‖ := mul_le_mul_of_nonneg_left (secondRestriction_norm_le b) (norm_nonneg _)
  · calc
      ‖A (riesz E (firstRestriction b))‖ ≤ ‖A‖ * ‖riesz E (firstRestriction b)‖ := A.le_opNorm _
      _ = ‖A‖ * ‖firstRestriction b‖ := by rw [riesz_norm]
      _ ≤ ‖A‖ * ‖b‖ := mul_le_mul_of_nonneg_left (firstRestriction_norm_le b) (norm_nonneg _)

theorem tensor_pairing (A : E →L[ℝ] F) (a b : (E × F) →L[ℝ] ℝ) :
    a (tensor A b) =
      -inner ℝ (A (riesz E (firstRestriction a))) (riesz F (secondRestriction b)) +
        inner ℝ (riesz F (secondRestriction a)) (A (riesz E (firstRestriction b))) := by
  rw [pairing_decompose, tensor_apply]
  simp only [Prod.fst, Prod.snd, ← riesz_pairing, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_right]

theorem tensor_skew (A : E →L[ℝ] F) : IsSkewPoissonTensor (tensor A) := by
  intro a b
  rw [tensor_pairing, tensor_pairing]
  rw [real_inner_comm (riesz F (secondRestriction a)) (A (riesz E (firstRestriction b))),
    real_inner_comm (riesz F (secondRestriction b)) (A (riesz E (firstRestriction a)))]
  ring

@[simp] theorem firstRestriction_fst (b : E →L[ℝ] ℝ) :
    firstRestriction (b.comp (ContinuousLinearMap.fst ℝ E F)) = b := by
  ext x
  rfl

@[simp] theorem secondRestriction_fst (b : E →L[ℝ] ℝ) :
    secondRestriction (b.comp (ContinuousLinearMap.fst ℝ E F)) = 0 := by
  ext y
  simp

@[simp] theorem firstRestriction_snd (b : F →L[ℝ] ℝ) :
    firstRestriction (b.comp (ContinuousLinearMap.snd ℝ E F)) = 0 := by
  ext x
  simp

@[simp] theorem secondRestriction_snd (b : F →L[ℝ] ℝ) :
    secondRestriction (b.comp (ContinuousLinearMap.snd ℝ E F)) = b := by
  ext y
  rfl

theorem tensor_fderiv_first (A : E →L[ℝ] F) {f : E → ℝ} (z : E × F)
    (hf : DifferentiableAt ℝ f z.1) :
    tensor A (fderiv ℝ (fun p : E × F => f p.1) z) = (0, A (gradient f z.1)) := by
  have hd := fderiv_comp (x := z) hf differentiableAt_fst
  simp only [fderiv_fst] at hd
  rw [show fderiv ℝ (fun p : E × F => f p.1) z =
      (fderiv ℝ f z.1).comp (ContinuousLinearMap.fst ℝ E F) from hd]
  simp [tensor_apply, riesz, gradient]

theorem tensor_fderiv_second (A : E →L[ℝ] F) {g : F → ℝ} (z : E × F)
    (hg : DifferentiableAt ℝ g z.2) :
    tensor A (fderiv ℝ (fun p : E × F => g p.2) z) = (-A.adjoint (gradient g z.2), 0) := by
  have hd := fderiv_comp (x := z) hg differentiableAt_snd
  simp only [fderiv_snd] at hd
  rw [show fderiv ℝ (fun p : E × F => g p.2) z =
      (fderiv ℝ g z.2).comp (ContinuousLinearMap.snd ℝ E F) from hd]
  simp [tensor_apply, riesz, gradient]

/-- Pullback by a projection of norm at most one preserves every derivative
bound; this transfers the marginal regularity assumption to the product. -/
theorem norm_iteratedFDeriv_pullback_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : X →L[ℝ] Y) (hP : ‖P‖ ≤ 1) {f : Y → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ s (f ∘ P) x‖ ≤ ‖iteratedFDeriv ℝ s f (P x)‖ := by
  rw [P.iteratedFDeriv_comp_right (i := s) hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ s f (P x)‖ * ∏ _i : Fin s, ‖P‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ s f (P x)‖ * ‖P‖ ^ s := by simp
    _ ≤ ‖iteratedFDeriv ℝ s f (P x)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hP) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_iteratedFDeriv_first_le {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℕ) (z : E × F) :
    ‖iteratedFDeriv ℝ s (fun p : E × F => f p.1) z‖ ≤
      ‖iteratedFDeriv ℝ s f z.1‖ :=
  norm_iteratedFDeriv_pullback_le (ContinuousLinearMap.fst ℝ E F)
    (ContinuousLinearMap.norm_fst_le ℝ E F) hf s z

theorem norm_iteratedFDeriv_second_le {g : F → ℝ}
    (hg : ContDiff ℝ ∞ g) (s : ℕ) (z : E × F) :
    ‖iteratedFDeriv ℝ s (fun p : E × F => g p.2) z‖ ≤
      ‖iteratedFDeriv ℝ s g z.2‖ :=
  norm_iteratedFDeriv_pullback_le (ContinuousLinearMap.snd ℝ E F)
    (ContinuousLinearMap.norm_snd_le ℝ E F) hg s z

end AltOMD.CoupledTensor
end
