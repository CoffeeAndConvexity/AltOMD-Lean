import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Ring

/-!
# Constant Poisson brackets

A constant Poisson tensor sends covectors to vectors. Its skewness is expressed by
the natural scalar pairing, so no choice of coordinates or nondegeneracy is needed.
The Jacobi identity below follows from the product rule and symmetry of second
Fréchet derivatives. In particular it applies to finite-dimensional real spaces.
-/

noncomputable section

open scoped ContDiff

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A constant tensor is skew with respect to evaluation of covectors on vectors. -/
def IsSkewPoissonTensor (J : (E →L[ℝ] ℝ) →L[ℝ] E) : Prop :=
  ∀ a b : E →L[ℝ] ℝ, a (J b) = -b (J a)

/-- The constant Poisson bracket, defined from actual Fréchet derivatives. -/
def poissonBracket (J : (E →L[ℝ] ℝ) →L[ℝ] E) (f g : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ f x (J (fderiv ℝ g x))

theorem poissonBracket_antisymm (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) (f g : E → ℝ) (x : E) :
    poissonBracket J f g x = -poissonBracket J g f x :=
  hJ _ _

/-- The product rule for a constant Poisson bracket. -/
theorem fderiv_poissonBracket_apply (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) (v : E) :
    fderiv ℝ (poissonBracket J f g) x v =
      fderiv ℝ f x (J (fderiv ℝ (fderiv ℝ g) x v)) +
        fderiv ℝ (fderiv ℝ f) x v (J (fderiv ℝ g x)) := by
  have h := hf.hasFDerivAt.clm_apply (J.hasFDerivAt.comp x hg.hasFDerivAt)
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) h.fderiv
  exact hv

/-- The nested-bracket formula used in the manuscript's Hessian proof. -/
theorem poissonBracket_nested (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) {f g k : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x)
    (hk : DifferentiableAt ℝ (fderiv ℝ k) x) :
    poissonBracket J f (poissonBracket J g k) x =
      fderiv ℝ (fderiv ℝ k) x (J (fderiv ℝ f x)) (J (fderiv ℝ g x)) -
        fderiv ℝ (fderiv ℝ g) x (J (fderiv ℝ f x)) (J (fderiv ℝ k x)) := by
  rw [poissonBracket_antisymm J hJ]
  change -fderiv ℝ (poissonBracket J g k) x (J (fderiv ℝ f x)) = _
  rw [fderiv_poissonBracket_apply J hg hk, hJ]
  ring

/-- Jacobi for twice continuously differentiable scalar functions at a point.
The smoothness assumptions supply the derivative formula and Hessian symmetry;
neither of these identities nor Jacobi is assumed. -/
theorem poissonBracket_jacobi_at (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) {f g k : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hk : ContDiffAt ℝ 2 k x) :
    poissonBracket J f (poissonBracket J g k) x +
      poissonBracket J g (poissonBracket J k f) x +
        poissonBracket J k (poissonBracket J f g) x = 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdk : DifferentiableAt ℝ (fderiv ℝ k) x :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [poissonBracket_nested J hJ hdg hdk,
    poissonBracket_nested J hJ hdk hdf, poissonBracket_nested J hJ hdf hdg]
  have hsf := hf.isSymmSndFDerivAt (by simp)
  have hsg := hg.isSymmSndFDerivAt (by simp)
  have hsk := hk.isSymmSndFDerivAt (by simp)
  rw [hsf (J (fderiv ℝ k x)) (J (fderiv ℝ g x)),
    hsg (J (fderiv ℝ f x)) (J (fderiv ℝ k x)),
    hsk (J (fderiv ℝ g x)) (J (fderiv ℝ f x))]
  ring

/-- The pointwise Jacobi identity for global `C²` functions. -/
theorem poissonBracket_jacobi (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) {f g k : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hk : ContDiff ℝ 2 k) (x : E) :
    poissonBracket J f (poissonBracket J g k) x +
      poissonBracket J g (poissonBracket J k f) x +
        poissonBracket J k (poissonBracket J f g) x = 0 :=
  poissonBracket_jacobi_at J hJ hf.contDiffAt hg.contDiffAt hk.contDiffAt

/-- The bracket of smooth scalar functions is smooth. -/
theorem poissonBracket_contDiff (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (poissonBracket J f g) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact hdf.clm_apply (J.contDiff.comp hdg)

/-- The Leibniz convolution bound for every derivative of a smooth Poisson bracket. -/
theorem norm_iteratedFDeriv_poissonBracket_le (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (s : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ s (poissonBracket J f g) x‖ ≤
      ‖J‖ * ∑ l ∈ Finset.range (s + 1),
        (s.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ *
          ‖iteratedFDeriv ℝ (s - l + 1) g x‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hprod := norm_iteratedFDeriv_clm_apply hdf (J.contDiff.comp hdg) x
    (N := ∞) (n := s) (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)
  change ‖iteratedFDeriv ℝ s (poissonBracket J f g) x‖ ≤ _ at hprod
  apply hprod.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hcomp := J.norm_iteratedFDeriv_comp_left hdg.contDiffAt
    (N := ∞) (n := s - l) (x := x)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl (s - l))
  have hterm := mul_le_mul_of_nonneg_left hcomp
    (show 0 ≤ (s.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ f) x‖ by positivity)
  simp only [norm_iteratedFDeriv_fderiv] at hterm ⊢
  convert hterm using 1 <;> ring

/-- Smooth scalar functions, viewed as a real vector subspace of all functions. -/
def smoothScalarSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (E → ℝ) where
  carrier := { f | ContDiff ℝ ∞ f }
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : E => (0 : ℝ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    change ContDiff ℝ ∞ (f + g)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ (c • f)
    exact ContDiff.const_smul c hf

/-- The vector space on which Hamiltonian Lie derivatives act. -/
abbrev SmoothScalar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ↥(smoothScalarSubmodule E)

theorem SmoothScalar.contDiff (f : SmoothScalar E) : ContDiff ℝ ∞ (f : E → ℝ) :=
  f.property

private theorem poissonBracket_add_left (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g k : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    poissonBracket J (fun y => f y + g y) k x =
      poissonBracket J f k x + poissonBracket J g k x := by
  unfold poissonBracket
  rw [fderiv_fun_add hf hg]
  simp

private theorem poissonBracket_add_right (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g k : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ g x) (hk : DifferentiableAt ℝ k x) :
    poissonBracket J f (fun y => g y + k y) x =
      poissonBracket J f g x + poissonBracket J f k x := by
  unfold poissonBracket
  rw [fderiv_fun_add hg hk]
  simp

private theorem poissonBracket_smul_left (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    poissonBracket J (fun y => c • f y) g x = c • poissonBracket J f g x := by
  unfold poissonBracket
  rw [fderiv_fun_const_smul hf c]
  simp

private theorem poissonBracket_smul_right (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    {f g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (c : ℝ) :
    poissonBracket J f (fun y => c • g y) x = c • poissonBracket J f g x := by
  unfold poissonBracket
  rw [fderiv_fun_const_smul hg c]
  simp

/-- The actual Poisson bracket as a bilinear map on smooth scalar functions. -/
def smoothPoissonBracket (J : (E →L[ℝ] ℝ) →L[ℝ] E) :
    SmoothScalar E →ₗ[ℝ] SmoothScalar E →ₗ[ℝ] SmoothScalar E where
  toFun f :=
    { toFun := fun g => ⟨poissonBracket J f g,
        poissonBracket_contDiff J f.contDiff g.contDiff⟩
      map_add' := by
        intro g k
        apply Subtype.ext
        funext x
        exact poissonBracket_add_right J
          (g.contDiff.differentiable (by simp) x) (k.contDiff.differentiable (by simp) x)
      map_smul' := by
        intro c g
        apply Subtype.ext
        funext x
        exact poissonBracket_smul_right J (g.contDiff.differentiable (by simp) x) c }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro k
    apply Subtype.ext
    funext x
    exact poissonBracket_add_left J
      (f.contDiff.differentiable (by simp) x) (g.contDiff.differentiable (by simp) x)
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext x
    exact poissonBracket_smul_left J (f.contDiff.differentiable (by simp) x) c

@[simp] theorem smoothPoissonBracket_apply (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (f g : SmoothScalar E) (x : E) :
    (smoothPoissonBracket J f g : E → ℝ) x = poissonBracket J f g x := rfl

theorem smoothPoissonBracket_antisymm (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) (f g : SmoothScalar E) :
    smoothPoissonBracket J f g = -smoothPoissonBracket J g f := by
  apply Subtype.ext
  funext x
  exact poissonBracket_antisymm J hJ f g x

theorem smoothPoissonBracket_jacobi (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) (f g k : SmoothScalar E) :
    smoothPoissonBracket J f (smoothPoissonBracket J g k) +
      smoothPoissonBracket J g (smoothPoissonBracket J k f) +
        smoothPoissonBracket J k (smoothPoissonBracket J f g) = 0 := by
  apply Subtype.ext
  funext x
  have h2 : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  exact poissonBracket_jacobi J hJ (f.contDiff.of_le h2)
    (g.contDiff.of_le h2) (k.contDiff.of_le h2) x

/-- `L_Q f = {f,Q}` on the vector space of smooth scalar functions. -/
def poissonGenerator (J : (E →L[ℝ] ℝ) →L[ℝ] E) (Q : SmoothScalar E) :
    Module.End ℝ (SmoothScalar E) := (smoothPoissonBracket J).flip Q

@[simp] theorem poissonGenerator_apply (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (Q f : SmoothScalar E) : poissonGenerator J Q f = smoothPoissonBracket J f Q := rfl

/-- The Hamiltonian/operator commutator identity, with the manuscript's sign convention. -/
theorem poissonGenerator_bracket (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hJ : IsSkewPoissonTensor J) (p q : SmoothScalar E) :
    poissonGenerator J (smoothPoissonBracket J q p) =
      poissonGenerator J p * poissonGenerator J q -
        poissonGenerator J q * poissonGenerator J p := by
  apply LinearMap.ext
  intro f
  change smoothPoissonBracket J f (smoothPoissonBracket J q p) =
    smoothPoissonBracket J (smoothPoissonBracket J f q) p -
      smoothPoissonBracket J (smoothPoissonBracket J f p) q
  have hJac := smoothPoissonBracket_jacobi J hJ f q p
  rw [smoothPoissonBracket_antisymm J hJ p f, map_neg,
    smoothPoissonBracket_antisymm J hJ q (smoothPoissonBracket J f p), neg_neg] at hJac
  apply eq_sub_iff_add_eq.mpr
  calc
    smoothPoissonBracket J f (smoothPoissonBracket J q p) +
        smoothPoissonBracket J (smoothPoissonBracket J f p) q =
        -smoothPoissonBracket J p (smoothPoissonBracket J f q) :=
          eq_neg_of_add_eq_zero_left hJac
    _ = smoothPoissonBracket J (smoothPoissonBracket J f q) p := by
      rw [smoothPoissonBracket_antisymm J hJ p (smoothPoissonBracket J f q), neg_neg]

end AltOMD
