import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Coefficientwise modified-energy preservation

Formal series are sequences, so every coefficient below is a finite sum. The
only external identity used by `preserved_of_formalBCH` is the substituted
formal BCH identity. In particular, preservation itself is proved here.
-/

namespace AltOMD
namespace FormalEnergy

open scoped BigOperators

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev Series (E : Type*) := ℕ → E

/-- A representative of a free Lie polynomial in the two update generators. -/
inductive LieExpression where
  | first : LieExpression
  | second : LieExpression
  | add : LieExpression → LieExpression → LieExpression
  | smul : ℝ → LieExpression → LieExpression
  | commutator : LieExpression → LieExpression → LieExpression

/-- Hamiltonian translation reverses the arguments of the Poisson bracket. -/
def LieExpression.hamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) :
    LieExpression → E
  | .first => G
  | .second => F
  | .add p q => p.hamiltonian B G F + q.hamiltonian B G F
  | .smul c p => c • p.hamiltonian B G F
  | .commutator p q => B (q.hamiltonian B G F) (p.hamiltonian B G F)

def LieExpression.operator (LG LF : Module.End ℝ E) : LieExpression → Module.End ℝ E
  | .first => LG
  | .second => LF
  | .add p q => p.operator LG LF + q.operator LG LF
  | .smul c p => c • p.operator LG LF
  | .commutator p q => p.operator LG LF * q.operator LG LF -
      q.operator LG LF * p.operator LG LF

/-- The Hamiltonian translation intertwines free Lie expressions and operators.
The hypothesis `hcomm` is the reversed-bracket commutator identity, derived
from Jacobi in the smooth Poisson module. -/
theorem LieExpression.translation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (L : E →ₗ[ℝ] Module.End ℝ E)
    (hcomm : ∀ p q, L (B q p) = L p * L q - L q * L p)
    (G F : E) (W : LieExpression) :
    W.operator (L G) (L F) = L (W.hamiltonian B G F) := by
  induction W with
  | first => rfl
  | second => rfl
  | add p q hp hq => simp [LieExpression.operator, LieExpression.hamiltonian, hp, hq]
  | smul c p hp => simp [LieExpression.operator, LieExpression.hamiltonian, hp]
  | commutator p q hp hq =>
    simp only [LieExpression.operator, LieExpression.hamiltonian, hp, hq, hcomm]

/-- The shift by one is the formal division of the BCH logarithm by `η`. -/
def correctedHamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (Z : ℕ → LieExpression) : Series E :=
  fun r => (Z (r + 1)).hamiltonian B G F

/-- The Cauchy extension of a bilinear bracket to formal series. -/
def bracket (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (P Q : Series E) : Series E :=
  fun n => ∑ p ∈ Finset.antidiagonal n, B (P p.1) (Q p.2)

theorem bracket_skew (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hB : ∀ x y, B x y = -B y x) (P Q : Series E) :
    bracket B P Q = -bracket B Q P := by
  funext n
  dsimp [bracket]
  rw [← Finset.sum_neg_distrib]
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, -B (Q p.2) (P p.1) :=
      Finset.sum_congr rfl (fun p _ => hB _ _)
    _ = _ := Finset.Nat.sum_antidiagonal_swap
      (n := n) (f := fun p => -B (Q p.1) (P p.2))

theorem bracket_self (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hB : ∀ x y, B x y = -B y x) (H : Series E) : bracket B H H = 0 := by
  funext n
  have h := congrFun (bracket_skew B hB H H) n
  have hz : (2 : ℝ) • bracket B H H n = 0 := by
    calc
      _ = bracket B H H n + bracket B H H n := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
      _ = bracket B H H n + (-bracket B H H n) :=
        congrArg (fun y : E => bracket B H H n + y) h
      _ = 0 := add_neg_cancel _
  calc
    bracket B H H n = (2 : ℝ)⁻¹ • ((2 : ℝ) • bracket B H H n) := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    _ = 0 := by rw [hz, smul_zero]

/-- Multiplication by the formal parameter. -/
def shift (P : Series E) : Series E
  | 0 => 0
  | n + 1 => P n

/-- The formal Hamiltonian generator `η L_H`. -/
def generator (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (H P : Series E) : Series E :=
  shift (bracket B P H)

@[simp] theorem generator_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (H : Series E) :
    generator B H 0 = 0 := by
  funext n
  cases n <;> simp [generator, shift, bracket]

theorem generator_self (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hB : ∀ x y, B x y = -B y x) (H : Series E) : generator B H H = 0 := by
  rw [generator, bracket_self B hB]
  funext n
  cases n <;> rfl

def actionPower (L : Series E → Series E) : ℕ → Series E → Series E
  | 0, P => P
  | k + 1, P => L (actionPower L k P)

theorem actionPower_annihilates (L : Series E → Series E) (H : Series E)
    (hzero : L 0 = 0) (hH : L H = 0) (k : ℕ) : actionPower L (k + 1) H = 0 := by
  induction k with
  | zero => exact hH
  | succ k ih =>
    change L (actionPower L (k + 1) H) = 0
    rw [ih, hzero]

/-- Coefficients of the exponential of an operator of positive formal order. -/
def expApply (L : Series E → Series E) (P : Series E) : Series E :=
  fun n => ∑ k ∈ Finset.range (n + 1), (1 / (k.factorial : ℝ)) • actionPower L k P n

theorem expApply_of_annihilates (L : Series E → Series E) (H : Series E)
    (hzero : L 0 = 0) (hH : L H = 0) : expApply L H = H := by
  funext n
  unfold expApply
  rw [Finset.sum_eq_single 0]
  · simp [actionPower]
  · intro k _ hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp [actionPower_annihilates L H hzero hH j]
  · simp

/-- Application of a formal operator series to a formal vector series. -/
def applySeries (U : ℕ → Module.End ℝ E) (H : Series E) : Series E :=
  fun n => ∑ r ∈ Finset.range (n + 1), U (n - r) (H r)

/-- Formal BCH is the sole input: after Hamiltonian translation, its logarithm
is `η L_H`. Antisymmetry proves that the resulting update preserves `H`. -/
theorem preserved_of_formalBCH
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hB : ∀ x y, B x y = -B y x)
    (H : Series E) (U : ℕ → Module.End ℝ E)
    (formalBCH : ∀ P, applySeries U P = expApply (generator B H) P) :
    applySeries U H = H := by
  rw [formalBCH]
  exact expApply_of_annihilates _ H (generator_zero B H) (generator_self B hB H)

/-- Extracting a positive-degree coefficient cancels the identity contribution. -/
theorem positive_coefficient_cancellation (U : ℕ → Module.End ℝ E)
    (hU : U 0 = LinearMap.id) (H : Series E) (hpres : applySeries U H = H)
    (j : ℕ) : ∑ r ∈ Finset.range j, U (j - r) (H r) = 0 := by
  have h := congrFun hpres j
  simp only [applySeries, Finset.sum_range_succ, Nat.sub_self, hU,
    LinearMap.id_apply] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

/-- The coefficients of `exp(η LG) exp(η LF)`, with operator multiplication
interpreted as composition. -/
def splitFlowCoefficient (LG LF : Module.End ℝ E) (n : ℕ) : Module.End ℝ E :=
  ∑ p ∈ Finset.antidiagonal n,
    (1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) • (LG ^ p.1 * LF ^ p.2)

@[simp] theorem splitFlowCoefficient_zero (LG LF : Module.End ℝ E) :
    splitFlowCoefficient LG LF 0 = LinearMap.id := by
  simp [splitFlowCoefficient]
  rfl

/-- The logarithm operator assembled from its positive-degree Lie coefficients. -/
def bchGenerator (Z : ℕ → LieExpression) (LG LF : Module.End ℝ E)
    (P : Series E) : Series E :=
  shift (applySeries (fun r => (Z (r + 1)).operator LG LF) P)

/-- The exponential-identity part of Proposition A.1, specialized to
endomorphisms. `BCHTheorem.classicalBCHInput` supplies this interface for the
canonical coefficients. It contains no preservation assertion and no bound. -/
structure ClassicalBCHInput (Z : ℕ → LieExpression) (E : Type*)
    [AddCommGroup E] [Module ℝ E] : Prop where
  linear_coefficient : Z 1 = .add .first .second
  exponentiate : ∀ (LG LF : Module.End ℝ E) (P : Series E),
    applySeries (splitFlowCoefficient LG LF) P = expApply (bchGenerator Z LG LF) P

theorem correctedHamiltonian_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (G F : E) (Z : ℕ → LieExpression) (bch : ClassicalBCHInput Z E) :
    correctedHamiltonian B G F Z 0 = F + G := by
  simp [correctedHamiltonian, bch.linear_coefficient, LieExpression.hamiltonian, add_comm]

theorem generator_translation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hcomm : ∀ p q, B.flip (B q p) = B.flip p * B.flip q - B.flip q * B.flip p)
    (G F : E) (Z : ℕ → LieExpression) :
    generator B (correctedHamiltonian B G F Z) = bchGenerator Z (B.flip G) (B.flip F) := by
  funext P n
  cases n with
  | zero => rfl
  | succ n =>
    change (∑ p ∈ Finset.antidiagonal n,
      B (P p.1) ((Z (p.2 + 1)).hamiltonian B G F)) =
      ∑ r ∈ Finset.range (n + 1), ((Z (n - r + 1)).operator (B.flip G) (B.flip F)) (P r)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => B (P i) ((Z (j + 1)).hamiltonian B G F)) n]
    apply Finset.sum_congr rfl
    intro r _
    rw [LieExpression.translation B B.flip hcomm]
    rfl

/-- Preservation for the actual Hamiltonian translation of the BCH coefficients. -/
theorem correctedHamiltonian_preserved
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hB : ∀ x y, B x y = -B y x)
    (hcomm : ∀ p q, B.flip (B q p) = B.flip p * B.flip q - B.flip q * B.flip p)
    (G F : E) (Z : ℕ → LieExpression) (bch : ClassicalBCHInput Z E) :
    applySeries (splitFlowCoefficient (B.flip G) (B.flip F))
      (correctedHamiltonian B G F Z) = correctedHamiltonian B G F Z := by
  apply preserved_of_formalBCH B hB
  intro P
  rw [bch.exponentiate, generator_translation B hcomm]

/-- The explicit double sum of Lie derivatives used by the analytic proof. -/
theorem splitFlow_cancellation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hB : ∀ x y, B x y = -B y x)
    (H : Series E) (LG LF : Module.End ℝ E)
    (formalBCH : ∀ P, applySeries (splitFlowCoefficient LG LF) P =
      expApply (generator B H) P) (j : ℕ) :
    (∑ r ∈ Finset.range j, ∑ p ∈ Finset.antidiagonal (j - r),
      (1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) •
        ((LG ^ p.1 * LF ^ p.2) (H r))) = 0 := by
  have hp := preserved_of_formalBCH B hB H _ formalBCH
  have hc := positive_coefficient_cancellation _ (splitFlowCoefficient_zero LG LF) H hp j
  simpa [splitFlowCoefficient, _root_.sum_apply] using hc

theorem correctedHamiltonian_cancellation
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hB : ∀ x y, B x y = -B y x)
    (hcomm : ∀ p q, B.flip (B q p) = B.flip p * B.flip q - B.flip q * B.flip p)
    (G F : E) (Z : ℕ → LieExpression) (bch : ClassicalBCHInput Z E) (j : ℕ) :
    (∑ r ∈ Finset.range j, ∑ p ∈ Finset.antidiagonal (j - r),
      (1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) •
        (((B.flip G) ^ p.1 * (B.flip F) ^ p.2) (correctedHamiltonian B G F Z r))) = 0 := by
  apply splitFlow_cancellation B hB
  intro P
  rw [bch.exponentiate, generator_translation B hcomm]

end
end FormalEnergy
end AltOMD
