import AltOMD.Hamiltonian.WordCoefficients

/-!
# Canonical expressions for the BCH Lie coefficients

The degree-`n` expression is the right-nested projection of the explicit
associative logarithm, divided by `n`. This file constructs the expressions
and proves their Hamiltonian representation and coefficient bounds.

`AltOMD.BCH` states Proposition A.1 in universal rational form.
`BCHTheorem.classicalBCHInput` connects it to the exponential identity for
these real Lie expressions. This module proves their Hamiltonian representation.
-/

namespace AltOMD.BCHCoefficients

open WordCoefficients FormalEnergy
open scoped BigOperators

noncomputable section

/-- Turn a word into a right-nested commutator expression. The empty word
has projection zero. -/
def wordExpression : Word → LieExpression
  | [] => .smul 0 .first
  | [b] => if b then .first else .second
  | b :: c :: w => .commutator (if b then .first else .second)
      (wordExpression (c :: w))

/-- The right-nested projection, with the coefficients left uncollected. -/
def polynomialExpression : Polynomial → LieExpression
  | [] => .smul 0 .first
  | (c, w) :: p => .add (.smul c (wordExpression w)) (polynomialExpression p)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem wordExpression_hamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (w : Word) :
    (wordExpression w).hamiltonian B G F = nestedHamiltonian B G F w := by
  induction w with
  | nil => simp [wordExpression, LieExpression.hamiltonian, nestedHamiltonian]
  | cons b w ih =>
    cases w with
    | nil => cases b <;> rfl
    | cons c w =>
      change B ((wordExpression (c :: w)).hamiltonian B G F)
        ((if b then LieExpression.first else .second).hamiltonian B G F) = _
      rw [ih]
      cases b <;> rfl

theorem polynomialExpression_hamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (p : Polynomial) :
    (polynomialExpression p).hamiltonian B G F = evaluateNested B G F p := by
  induction p with
  | nil => simp [polynomialExpression, LieExpression.hamiltonian, evaluateNested]
  | cons t p ih =>
    simp [polynomialExpression, LieExpression.hamiltonian,
      wordExpression_hamiltonian, evaluateNested, ih]

@[simp] theorem evaluateNested_scale (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (c : ℝ) (p : Polynomial) :
    evaluateNested B G F (scale c p) = c • evaluateNested B G F p := by
  induction p with
  | nil => simp [scale, evaluateNested]
  | cons t p ih =>
    change (c * t.1) • nestedHamiltonian B G F t.2 +
      evaluateNested B G F (scale c p) =
        c • (t.1 • nestedHamiltonian B G F t.2 + evaluateNested B G F p)
    rw [ih, smul_add, mul_smul]

private theorem mul_one (p : Polynomial) : WordCoefficients.mul p one = p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change prepend t.1 t.2 one ++ WordCoefficients.mul p one = t :: p
    rw [ih]
    simp [one, prepend]

private theorem composition_one_eq (c : Composition 1) : c = Composition.ones 1 := by
  apply Composition.eq_ones_iff.mpr
  intro i hi
  have := c.blocks_le hi
  have := c.one_le_blocks hi
  omega

theorem evaluateNested_logarithm_one (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) :
    evaluateNested B G F (logarithm 1) = G + F := by
  classical
  have hu : (Finset.univ : Finset (Composition 1)) = {Composition.ones 1} := by
    ext c
    simp [composition_one_eq c]
  rw [logarithm, hu]
  simp only [Finset.toList_singleton, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Composition.ones_blocks]
  simp only [List.replicate_succ, List.replicate_zero, List.length_cons,
    List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  norm_num only [List.map_cons, List.map_nil, product, mul_one, evaluateNested_scale,
    zero_add, neg_one_sq, div_one, one_smul]
  rw [exponential, evaluateNested_eq_sum, List.map_map]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp [Finset.sum_range_succ, nestedHamiltonian, add_comm]

@[simp] theorem evaluateNested_correction_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) :
    evaluateNested B G F (correctionRepresentation 0) = G + F := by
  simp [correctionRepresentation, evaluateNested_logarithm_one]

/-- Canonical Dynkin expressions. The degree-one expression is normalized
syntactically to the interface required by `ClassicalBCHInput`. -/
def coefficient : ℕ → LieExpression
  | 0 => .smul 0 .first
  | 1 => .add .first .second
  | n + 2 => polynomialExpression (correctionRepresentation (n + 1))

@[simp] theorem coefficient_one : coefficient 1 = .add .first .second := rfl

theorem coefficient_hamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) (r : ℕ) :
    (coefficient (r + 1)).hamiltonian B G F =
      evaluateNested B G F (correctionRepresentation r) := by
  cases r with
  | zero => simp [coefficient, LieExpression.hamiltonian]
  | succ r => exact polynomialExpression_hamiltonian B G F _

/-- The Hamiltonian representation from Dynkin's formula for the canonical
expressions. No skew-symmetry or Jacobi assumption is needed for this
structural identity. The historical name is retained for compatibility. -/
theorem classicalDSWInput : ClassicalDSWInput coefficient E where
  representation B _ _ G F r := coefficient_hamiltonian B G F r

end
end AltOMD.BCHCoefficients
