import AltOMD.Hamiltonian.WordCoefficients
import AltOMD.Algebra.CompositionCoefficients
import AltOMD.Algebra.NoncommutativeExponential
import Mathlib.Algebra.Module.Rat

/-!
# The word expansion is the formal BCH logarithm

The composition formula for the explicit word coefficients agrees with the
formal logarithm of `exp(t U) exp(t V)` in every real associative algebra.
No Lie-membership assertion is used by this identification.
-/

namespace AltOMD.BCHLogarithm

open scoped BigOperators
open WordCoefficients

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

local instance : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℝ)

private theorem list_sum_finset {B ι : Type*} [AddCommMonoid B]
    (s : Finset ι) (f : ι → B) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  simp

theorem evaluate_map (U V : A) {ι : Type*} (l : List ι) (f : ι → ℝ × Word) :
    evaluate U V (l.map f) =
      (l.map fun i => (f i).1 • evaluateWord U V (f i).2).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [evaluate, ih]

theorem evaluate_flatMap (U V : A) {ι : Type*} (l : List ι)
    (f : ι → WordCoefficients.Polynomial) :
    evaluate U V (l.flatMap f) = (l.map fun i => evaluate U V (f i)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [evaluate_append, ih]

theorem evaluate_product (U V : A) (ps : List WordCoefficients.Polynomial) :
    evaluate U V (product ps) = (ps.map (evaluate U V)).prod := by
  induction ps with
  | nil => simp [product, one, evaluate, evaluateWord]
  | cons p ps ih => simp [product, evaluate_mul, ih]

theorem evaluate_exponential (U V : A) (n : ℕ) :
    evaluate U V (exponential n) =
      ∑ j ∈ Finset.range (n + 1),
        (1 / ((j.factorial : ℝ) * ((n - j).factorial : ℝ))) •
          (U ^ j * V ^ (n - j)) := by
  rw [exponential, evaluate_map, list_sum_finset]
  apply Finset.sum_congr rfl
  intro j hj
  simp [evaluateWord]

theorem evaluate_logarithm (U V : A) (n : ℕ) :
    evaluate U V (logarithm n) =
      ∑ c : Composition n,
        ((-1 : ℝ) ^ (c.length + 1) / (c.length : ℝ)) •
          (c.blocks.map fun j => evaluate U V (exponential j)).prod := by
  rw [logarithm, evaluate_flatMap, list_sum_finset]
  simp only [evaluate_scale, evaluate_product, List.map_map, Composition.blocks_length]
  rfl

/-- The formal product of the two exponential word series. -/
def splitSeries (U V : A) : PowerSeries A :=
  PowerSeries.mk fun n => evaluate U V (exponential n)

@[simp] theorem coeff_splitSeries (U V : A) (n : ℕ) :
    PowerSeries.coeff n (splitSeries U V) = evaluate U V (exponential n) :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_splitSeries (U V : A) :
    (splitSeries U V).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_splitSeries,
    evaluate_exponential]
  simp

/-- The composition-indexed word formula is exactly the formal logarithm
coefficient, including degree zero. -/
theorem coeff_logOf_splitSeries (U V : A) (n : ℕ) :
    PowerSeries.coeff n (NoncommutativeSeries.logOf (splitSeries U V)) =
      evaluate U V (logarithm n) := by
  have hp : (splitSeries U V - 1).constantCoeff = 0 := by simp
  rw [NoncommutativeSeries.coeff_logOf,
    CompositionCoefficients.weighted_coeff_pow_sum _ hp,
    evaluate_logarithm]
  apply Finset.sum_congr rfl
  intro c hc
  have hcoeff :
      (c.blocks.map fun j => PowerSeries.coeff j (splitSeries U V - 1)).prod =
        (c.blocks.map fun j => evaluate U V (exponential j)).prod := by
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj0 : j ≠ 0 := Nat.ne_of_gt (c.blocks_pos hj)
    simp [PowerSeries.coeff_one, hj0]
  have hscalar (q : ℚ) (a : A) : q • a = (q : ℝ) • a := rfl
  rw [hcoeff, hscalar]
  by_cases hk : c.length = 0 <;> simp [hk]

omit [Algebra ℝ A] in
/-- Powers of a linear monomial, without commutative coefficients. -/
theorem monomial_one_pow (U : A) (n : ℕ) :
    (PowerSeries.monomial 1 U) ^ n = PowerSeries.monomial n (U ^ n) := by
  induction n with
  | zero => simp [PowerSeries.monomial_zero_eq_C_apply]
  | succ n ih => rw [pow_succ, ih, PowerSeries.monomial_mul_monomial, pow_succ]

/-- A linear monomial has the expected formal exponential coefficients. -/
theorem coeff_expOf_monomial_one (U : A) (n : ℕ) :
    PowerSeries.coeff n
      (NoncommutativeSeries.expOf (PowerSeries.monomial 1 U)) =
        (1 / (n.factorial : ℝ)) • U ^ n := by
  rw [NoncommutativeSeries.coeff_expOf]
  simp only [monomial_one_pow, PowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single n]
  · rw [if_pos rfl]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      (ratCast_smul_eq ℝ ℚ (1 / (n.factorial : ℚ)) (U ^ n)).symm
  · intro k hk hkn
    simp [Ne.symm hkn]
  · simp

/-- The explicit exponential word series is the actual product of two formal
exponentials, with multiplication in the stated order. -/
theorem splitSeries_eq_expOf_mul (U V : A) :
    splitSeries U V =
      NoncommutativeSeries.expOf (PowerSeries.monomial 1 U) *
        NoncommutativeSeries.expOf (PowerSeries.monomial 1 V) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_splitSeries, evaluate_exponential, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_expOf_monomial_one, coeff_expOf_monomial_one]
  simp [smul_smul]

/-- Explicit word coefficients of the formal BCH series for two generators. -/
theorem coeff_bch_monomial_one (U V : A) (n : ℕ) :
    PowerSeries.coeff n
      (NoncommutativeSeries.bch (PowerSeries.monomial 1 U)
        (PowerSeries.monomial 1 V)) = evaluate U V (logarithm n) := by
  rw [NoncommutativeSeries.bch, ← splitSeries_eq_expOf_mul,
    coeff_logOf_splitSeries]

/-- The operator coefficients used in the alternating-flow proof are the
same formal product coefficients. -/
theorem coeff_splitSeries_end {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U V : Module.End ℝ E) (n : ℕ) :
    PowerSeries.coeff n (splitSeries U V) =
      FormalEnergy.splitFlowCoefficient U V n := by
  rw [coeff_splitSeries, evaluate_exponential, FormalEnergy.splitFlowCoefficient,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end

end AltOMD.BCHLogarithm
