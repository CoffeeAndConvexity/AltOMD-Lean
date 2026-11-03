import AltOMD.Algebra.NoncommutativeExponential
import AltOMD.Algebra.BCHLieCriterion

/-!
# Homogeneity of the formal BCH coefficients

Central rational rescaling of the formal variable works for noncommutative
coefficient rings. It commutes with formal exponential and logarithm, so the
degree-`n` coefficient of BCH on linear inputs is homogeneous of degree `n`.
The final membership criterion retains its four-term-defect hypothesis
explicitly; this file does not prove unconditional Lie membership.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Rescale the formal variable by a central rational scalar. -/
def rescale (c : ℚ) : PowerSeries A →ₐ[ℚ] PowerSeries A where
  toFun p := PowerSeries.mk fun n => c ^ n • PowerSeries.coeff n p
  map_zero' := by ext n; simp
  map_add' p q := by ext n; simp [smul_add]
  map_one' := by
    ext n
    cases n <;> simp [PowerSeries.coeff_one]
  map_mul' p q := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add,
      Finset.mem_antidiagonal.mp hij]
  commutes' r := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
    split_ifs with h
    · subst n; rw [pow_zero, one_smul]
    · rw [smul_zero]

@[simp] theorem coeff_rescale (c : ℚ) (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (rescale c p) = c ^ n • PowerSeries.coeff n p := by
  change PowerSeries.coeff n (PowerSeries.mk fun k => c ^ k • PowerSeries.coeff k p) = _
  exact PowerSeries.coeff_mk n _

@[simp] theorem constantCoeff_rescale (c : ℚ) (p : PowerSeries A) :
    (rescale c p).constantCoeff = p.constantCoeff := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_smul]
    using coeff_rescale c p 0

theorem rescale_eval (c : ℚ) (p : PowerSeries A) (f : PowerSeries ℚ) :
    rescale c (eval p f) = eval (rescale c p) f := by
  ext n
  rw [coeff_rescale, coeff_eval_eq_sum, coeff_eval_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← map_pow, coeff_rescale, smul_comm]

theorem rescale_expOf (c : ℚ) (p : PowerSeries A) :
    rescale c (expOf p) = expOf (rescale c p) :=
  rescale_eval c p _

theorem rescale_logOf (c : ℚ) (p : PowerSeries A) :
    rescale c (logOf p) = logOf (rescale c p) := by
  simp only [logOf, rescale_eval, map_sub, map_one]

theorem rescale_bch (c : ℚ) (p q : PowerSeries A) :
    rescale c (bch p q) = bch (rescale c p) (rescale c q) := by
  simp only [bch, rescale_logOf, map_mul, rescale_expOf]

@[simp] theorem rescale_monomial (c : ℚ) (n : ℕ) (a : A) :
    rescale c (PowerSeries.monomial n a) = PowerSeries.monomial n (c ^ n • a) := by
  ext k
  by_cases h : k = n
  · subst k; simp
  · simp [PowerSeries.coeff_monomial, h]

omit [Algebra ℚ A] in
@[simp] theorem constantCoeff_monomial_one (a : A) :
    (PowerSeries.monomial 1 a).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial]
  rfl

/-- The associative degree-`n` BCH coefficient for two constant generators. -/
def bchCoefficient (n : ℕ) (a b : A) : A :=
  PowerSeries.coeff n (bch (PowerSeries.monomial 1 a) (PowerSeries.monomial 1 b))

/-- Simultaneously scaling the two generators multiplies the degree-`n`
coefficient by the `n`-th power of the scalar. -/
theorem bchCoefficient_smul (c : ℚ) (n : ℕ) (a b : A) :
    bchCoefficient n (c • a) (c • b) = c ^ n • bchCoefficient n a b := by
  have h := congrArg (PowerSeries.coeff n)
    (rescale_bch c (PowerSeries.monomial 1 a) (PowerSeries.monomial 1 b))
  simpa only [coeff_rescale, rescale_monomial, pow_one, bchCoefficient] using h.symm

/-- The diagonal BCH coefficients vanish beyond the linear term. -/
theorem bchCoefficient_self (n : ℕ) (hn : n ≠ 1) (a : A) :
    bchCoefficient n a a = 0 := by
  unfold bchCoefficient
  rw [bch_self (by simp)]
  simp [PowerSeries.coeff_monomial, hn]

/-- Interchanging the generators changes the degree-`n` coefficient by the
usual alternating sign. -/
theorem bchCoefficient_swap (n : ℕ) (a b : A) :
    bchCoefficient n b a = -((-1 : ℚ) ^ n • bchCoefficient n a b) := by
  have hneg : bchCoefficient n (-a) (-b) = -bchCoefficient n b a := by
    unfold bchCoefficient
    simp only [map_neg]
    rw [bch_neg _ _ (by simp) (by simp), map_neg]
  have hhom := bchCoefficient_smul (-1) n a b
  simp only [neg_one_smul] at hhom
  calc
    bchCoefficient n b a = -bchCoefficient n (-a) (-b) := by rw [hneg, neg_neg]
    _ = -((-1 : ℚ) ^ n • bchCoefficient n a b) := congrArg Neg.neg hhom

/-- The final BCH Lie-membership step, reduced to the four-term defect.
The remaining hypothesis must be established from the lower-degree Lie
coefficients by a formal-series substitution argument; it is not asserted here. -/
theorem bchCoefficient_mem_of_four_term (S W : Submodule ℚ A)
    (n : ℕ) (hn : 2 < n)
    (hfour : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W,
      BCHLieCriterion.fourTermDefect (bchCoefficient n) a b c d ∈ S)
    {a b : A} (ha : a ∈ W) (hb : b ∈ W) : bchCoefficient n a b ∈ S := by
  apply BCHLieCriterion.mem_of_four_term S W (bchCoefficient n) n hn
    (fun x _ => bchCoefficient_self n (by omega) x)
    (fun x _ y _ => bchCoefficient_smul 2 n x y)
    (fun x _ y _ => bchCoefficient_swap n x y) hfour ha hb

end
end AltOMD.NoncommutativeSeries
