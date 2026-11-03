import AltOMD.Hamiltonian.BCHTheorem
import AltOMD.Hamiltonian.BilinearSystem
import AltOMD.Hamiltonian.EnergyDefect
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical modified Hamiltonian and its coefficient identities

These declarations fix the proved BCH coefficients internally. No BCH,
Dynkin, Jacobi, or cancellation premise is required from a caller. Formal
pullback means the coefficientwise ordered Lie expansion of the actual split
flows; it does not assert convergence of the modified-Hamiltonian series.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace AltOMD.CoupledTensor

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedSpace ℝ F := InnerProductSpace.toNormedSpace

/-- The tensor used on the maximum-norm product has exactly the game's
operator norm. Testing covectors supported on the first coordinate proves
the reverse of `tensor_norm_le`. -/
theorem tensor_norm_eq (A : E →L[ℝ] F) : ‖tensor A‖ = ‖A‖ := by
  apply le_antisymm (tensor_norm_le A)
  apply A.opNorm_le_bound (norm_nonneg (tensor A))
  intro x
  let b := (InnerProductSpace.toDual ℝ E x).comp (ContinuousLinearMap.fst ℝ E F)
  have hfirst : firstRestriction b = InnerProductSpace.toDual ℝ E x := by
    ext y
    rfl
  have hriesz : riesz E (InnerProductSpace.toDual ℝ E x) = x := by
    change (InnerProductSpace.toDual ℝ E).symm (InnerProductSpace.toDual ℝ E x) = x
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply x
  have htest : (tensor A b).2 = A x := by
    simp only [tensor_apply, hfirst, hriesz]
  have hb : ‖b‖ ≤ ‖x‖ := by
    calc
      ‖b‖ ≤ ‖InnerProductSpace.toDual ℝ E x‖ * ‖ContinuousLinearMap.fst ℝ E F‖ :=
        (InnerProductSpace.toDual ℝ E x).opNorm_comp_le _
      _ ≤ ‖x‖ * 1 := by
        rw [(InnerProductSpace.toDual ℝ E).norm_map]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le ℝ E F) (norm_nonneg x)
      _ = ‖x‖ := mul_one _
  calc
    ‖A x‖ = ‖(tensor A b).2‖ := by rw [htest]
    _ ≤ ‖tensor A b‖ := norm_snd_le _
    _ ≤ ‖tensor A‖ * ‖b‖ := (tensor A).le_opNorm b
    _ ≤ ‖tensor A‖ * ‖x‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg (tensor A))

end AltOMD.CoupledTensor

namespace AltOMD.CanonicalHamiltonian

section Bracket

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The degree-`r` Hamiltonian coefficient, with its additive normalization
fixed by the explicit BCH word formula. -/
def correction (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (G F : V) (r : ℕ) : V :=
  FormalEnergy.correctedHamiltonian B G F BCHCoefficients.coefficient r

/-- The defining coefficient formula; it fixes constants and Casimirs too. -/
theorem correction_eq_nested (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (G F : V) (r : ℕ) :
    correction B G F r = WordCoefficients.evaluateNested B G F
      (WordCoefficients.correctionRepresentation r) :=
  BCHCoefficients.coefficient_hamiltonian B G F r

@[simp] theorem correction_zero (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (G F : V) :
    correction B G F 0 = F + G :=
  FormalEnergy.correctedHamiltonian_zero B G F _ BCHTheorem.classicalBCHInput

/-- Reversing the Poisson bracket at each of the `length - 1` internal
vertices explains the global sign in the manuscript formula. -/
theorem nestedHamiltonian_eq_signed_flip
    (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (hB : ∀ x y, B x y = -B y x)
    (G F : V) (w : WordCoefficients.Word) :
    WordCoefficients.nestedHamiltonian B G F w =
      (-1 : ℝ) ^ (w.length - 1) • WordCoefficients.nestedHamiltonian B.flip G F w := by
  induction w with
  | nil => simp [WordCoefficients.nestedHamiltonian]
  | cons b w ih =>
    cases w with
    | nil => simp [WordCoefficients.nestedHamiltonian]
    | cons c w =>
      change B (WordCoefficients.nestedHamiltonian B G F (c :: w))
        (if b then G else F) =
          (-1 : ℝ) ^ (w.length + 1) •
            B (if b then G else F)
              (WordCoefficients.nestedHamiltonian B.flip G F (c :: w))
      rw [ih]
      simp only [List.length_cons, Nat.add_sub_cancel, map_smul,
        LinearMap.smul_apply]
      rw [hB]
      simp [pow_succ, smul_smul, smul_neg]

/-- Using `B.flip` in the internal evaluator is ordinary right nesting for
`B`. The last word is nonempty, exactly as in the source convention. -/
theorem ordinary_nested_cons (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (G F : V)
    (b : Bool) (w : WordCoefficients.Word) (hw : w ≠ []) :
    WordCoefficients.nestedHamiltonian B.flip G F (b :: w) =
      B (if b then G else F) (WordCoefficients.nestedHamiltonian B.flip G F w) :=
  WordCoefficients.nestedHamiltonian_cons B.flip G F b w hw

/-- The finite coefficient list for ordinary right-nested Poisson brackets.
Repeated words remain separate summands; its mass is an upper bound on the
mass after collection. Every word has positive length. -/
def ordinaryRepresentation (r : ℕ) : WordCoefficients.Polynomial :=
  WordCoefficients.scale ((-1 : ℝ) ^ r) (WordCoefficients.correctionRepresentation r)

/-- Source-facing correction formula, word length, and coefficient bound.
The signed list evaluates using ordinary right-nested brackets of `B`. -/
theorem correction_representation_and_bound
    (B : V →ₗ[ℝ] V →ₗ[ℝ] V) (hB : ∀ x y, B x y = -B y x)
    (G F : V) (r : ℕ) :
    correction B G F r =
        WordCoefficients.evaluateNested B.flip G F (ordinaryRepresentation r) ∧
      WordCoefficients.Homogeneous (r + 1) (ordinaryRepresentation r) ∧
      WordCoefficients.mass (ordinaryRepresentation r) ≤ (4 : ℝ) ^ (r + 1) := by
  refine ⟨?_, WordCoefficients.homogeneous_scale _ _ _
    (WordCoefficients.correctionRepresentation_homogeneous r), ?_⟩
  · have he : ∀ p : WordCoefficients.Polynomial,
        WordCoefficients.Homogeneous (r + 1) p →
        WordCoefficients.evaluateNested B G F p =
          (-1 : ℝ) ^ r • WordCoefficients.evaluateNested B.flip G F p := by
      intro p
      induction p with
      | nil => intro _; simp [WordCoefficients.evaluateNested]
      | cons t p ih =>
        intro hp
        have ht := hp t (by simp)
        have hp' : WordCoefficients.Homogeneous (r + 1) p :=
          fun u hu => hp u (by simp [hu])
        simp only [WordCoefficients.evaluateNested, ih hp', smul_add]
        rw [nestedHamiltonian_eq_signed_flip B hB G F t.2, ht]
        simp only [Nat.add_sub_cancel, smul_smul]
        rw [mul_comm t.1]
    rw [correction_eq_nested, ordinaryRepresentation, BCHCoefficients.evaluateNested_scale]
    exact he _ (WordCoefficients.correctionRepresentation_homogeneous r)
  · simp only [ordinaryRepresentation, WordCoefficients.mass_scale, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact WordCoefficients.correctionRepresentation_mass_le r

end Bracket

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Canonical coefficients for a specified split system. -/
def coefficients (S : SplitHamiltonianSystem E) : ℕ → SmoothScalar E :=
  correction (smoothPoissonBracket S.J) S.G S.F

@[simp] theorem coefficients_zero (S : SplitHamiltonianSystem E) :
    coefficients S 0 = S.F + S.G := correction_zero _ _ _

/-- The coefficient normalization agrees with the BCH operator logarithm. -/
theorem coefficient_generator (S : SplitHamiltonianSystem E) (r : ℕ) :
    (BCHCoefficients.coefficient (r + 1)).operator
      (poissonGenerator S.J S.G) (poissonGenerator S.J S.F) =
        poissonGenerator S.J (coefficients S r) :=
  FormalEnergy.LieExpression.translation (smoothPoissonBracket S.J)
    (smoothPoissonBracket S.J).flip (poissonGenerator_bracket S.J S.skew)
    S.G S.F _

/-- Ordered formal pullback by the split update. Multiplication of operators
is composition, hence the outer generator is `G` and the inner one is `F`. -/
def formalPullback (S : SplitHamiltonianSystem E)
    (H : FormalEnergy.Series (SmoothScalar E)) : FormalEnergy.Series (SmoothScalar E) :=
  FormalEnergy.applySeries
    (FormalEnergy.splitFlowCoefficient (poissonGenerator S.J S.G)
      (poissonGenerator S.J S.F)) H

/-- This coefficient equation states the formal-pullback representation
explicitly, in terms of the actual Hamiltonian vector fields. -/
theorem formalPullback_coefficient (S : SplitHamiltonianSystem E)
    (H : FormalEnergy.Series (SmoothScalar E)) (q : ℕ) (z : E) :
    (formalPullback S H q : E → ℝ) z =
      ∑ r ∈ Finset.range (q + 1),
        EnergyDefect.splitCoefficient (hamiltonianField S.J S.F)
          (hamiltonianField S.J S.G) (H r : E → ℝ) (q - r) z := by
  let ev : SmoothScalar E →ₗ[ℝ] ℝ :=
    { toFun := fun f => (f : E → ℝ) z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (formalPullback S H q) = _
  simp only [formalPullback, FormalEnergy.applySeries,
    FormalEnergy.splitFlowCoefficient, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [EnergyDefect.splitCoefficient_eq_antidiagonal]
  apply Finset.sum_congr rfl
  intro p _
  change (1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) *
    (((poissonGenerator S.J S.G ^ p.1 * poissonGenerator S.J S.F ^ p.2)
      (H r) : SmoothScalar E) : E → ℝ) z = _
  simp only [mixed_lieIterate_hamiltonianField, poissonGenerator,
    div_eq_mul_inv, one_mul, mul_one, mul_comm]

/-- Canonical formal preservation: all algebraic inputs are proved internally. -/
theorem formal_preservation (S : SplitHamiltonianSystem E) :
    formalPullback S (coefficients S) = coefficients S :=
  FormalEnergy.correctedHamiltonian_preserved (smoothPoissonBracket S.J)
    (smoothPoissonBracket_antisymm S.J S.skew) (poissonGenerator_bracket S.J S.skew)
    S.G S.F BCHCoefficients.coefficient BCHTheorem.classicalBCHInput

/-- Truncation as a formal series, with exactly the coefficients through `N`. -/
def truncatedSeries (S : SplitHamiltonianSystem E) (N : ℕ) :
    FormalEnergy.Series (SmoothScalar E) :=
  fun r => if r ≤ N then coefficients S r else 0

/-- The formal defect is `O(η^(N+2))`: every coefficient through `N+1`
vanishes, including degree zero. This is a statement about formal order. -/
theorem truncated_defect_coefficient_eq_zero (S : SplitHamiltonianSystem E)
    (N q : ℕ) (hq : q ≤ N + 1) :
    formalPullback S (truncatedSeries S N) q - truncatedSeries S N q = 0 := by
  have hc := FormalEnergy.positive_coefficient_cancellation
    (FormalEnergy.splitFlowCoefficient (poissonGenerator S.J S.G)
      (poissonGenerator S.J S.F))
    (FormalEnergy.splitFlowCoefficient_zero _ _) (coefficients S)
    (formal_preservation S) q
  unfold formalPullback FormalEnergy.applySeries
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, FormalEnergy.splitFlowCoefficient_zero,
    LinearMap.id_apply, add_sub_cancel_right]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [truncatedSeries, if_pos (by have := Finset.mem_range.mp hr; omega)]

/-- Canonical form of the separate coefficient representation lemma. -/
theorem coefficients_representation_and_bound (S : SplitHamiltonianSystem E) (r : ℕ) :
    coefficients S r = WordCoefficients.evaluateNested (smoothPoissonBracket S.J).flip
        S.G S.F (ordinaryRepresentation r) ∧
      WordCoefficients.Homogeneous (r + 1) (ordinaryRepresentation r) ∧
      WordCoefficients.mass (ordinaryRepresentation r) ≤ (4 : ℝ) ^ (r + 1) :=
  correction_representation_and_bound _ (smoothPoissonBracket_antisymm S.J S.skew) _ _ r

/-- Every positive-degree defect coefficient is zero. -/
theorem scalar_cancellation (S : SplitHamiltonianSystem E) (j : ℕ) (z : E) :
    (∑ r ∈ Finset.range j,
      EnergyDefect.splitCoefficient (hamiltonianField S.J S.F) (hamiltonianField S.J S.G)
        (coefficients S r : E → ℝ) (j - r) z) = 0 :=
  EnergyDefect.corrected_scalar_cancellation S.J S.skew S.G S.F
    BCHCoefficients.coefficient BCHTheorem.classicalBCHInput j z

/-- Exact cancellation of the finite Taylor polynomial through degree `N+1`.
This includes `N = 0` and requires no convergence assumption. -/
theorem truncation_cancellation (S : SplitHamiltonianSystem E)
    (N : ℕ) (h : ℝ) (z : E) :
    (∑ r ∈ Finset.range (N + 1), h ^ r *
      (Flow.triangularTaylor (hamiltonianField S.J S.F) (hamiltonianField S.J S.G)
        (coefficients S r : E → ℝ) (N + 1 - r) h z - (coefficients S r : E → ℝ) z)) = 0 := by
  apply EnergyDefect.weighted_triangular_cancellation
  intro j _
  exact scalar_cancellation S (j + 1) z

end Smooth

section Bilinear

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin m)

/-- The manuscript's formal preservation lemma for actual bilinear shears.
The system, skew tensor, flow laws, and BCH coefficients are constructed in
the conclusion, so the only functional premises are source smoothness. -/
theorem bilinear_formal_preservation (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    formalPullback (BilinearSystem.system A f g hf hg)
      (coefficients (BilinearSystem.system A f g hf hg)) =
        coefficients (BilinearSystem.system A f g hf hg) :=
  formal_preservation _

/-- The separately stated correction lemma for the same actual game. -/
theorem bilinear_correction_representation_and_bound
    (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (r : ℕ) :
    coefficients (BilinearSystem.system A f g hf hg) r =
        WordCoefficients.evaluateNested (smoothPoissonBracket (CoupledTensor.tensor A)).flip
          (BilinearSystem.secondHamiltonian g hg) (BilinearSystem.firstHamiltonian f hf)
          (ordinaryRepresentation r) ∧
      WordCoefficients.Homogeneous (r + 1) (ordinaryRepresentation r) ∧
      WordCoefficients.mass (ordinaryRepresentation r) ≤ (4 : ℝ) ^ (r + 1) :=
  coefficients_representation_and_bound _ r

/-- The finite formal defect cancellation for the same actual game. -/
theorem bilinear_truncation_cancellation (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (N : ℕ) (h : ℝ) (z : E × F) :
    let S := BilinearSystem.system A f g hf hg
    (∑ r ∈ Finset.range (N + 1), h ^ r *
      (Flow.triangularTaylor (hamiltonianField S.J S.F) (hamiltonianField S.J S.G)
        (coefficients S r : E × F → ℝ) (N + 1 - r) h z -
          (coefficients S r : E × F → ℝ) z)) = 0 :=
  truncation_cancellation _ N h z

/-- Exact formal-order claim for the actual bilinear update. -/
theorem bilinear_truncated_defect_coefficient_eq_zero
    (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (N q : ℕ) (hq : q ≤ N + 1) :
    let S := BilinearSystem.system A f g hf hg
    formalPullback S (truncatedSeries S N) q - truncatedSeries S N q = 0 :=
  truncated_defect_coefficient_eq_zero _ N q hq

end Bilinear
end AltOMD.CanonicalHamiltonian
