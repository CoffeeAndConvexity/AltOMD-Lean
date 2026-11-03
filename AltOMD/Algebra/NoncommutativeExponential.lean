import AltOMD.Algebra.NoncommutativeSeries
import AltOMD.Algebra.BCHSeries

/-!
# Formal exponential and logarithm in a noncommutative algebra

The coefficients lie in an arbitrary rational algebra.  The results are exact
formal identities: no norm, topology, or analytic convergence is required.
They establish the exponential/logarithm part of BCH.  They do not assert that
the logarithm of a product of exponentials has Lie-polynomial coefficients.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Formal exponential, meaningful on series with zero constant coefficient. -/
def expOf (p : PowerSeries A) : PowerSeries A := eval p (PowerSeries.exp ℚ)

/-- Formal logarithm, meaningful on series with constant coefficient one. -/
def logOf (u : PowerSeries A) : PowerSeries A := eval (u - 1) (PowerSeries.log ℚ)

/-- Scaling the input is scalar rescaling before evaluation. -/
theorem eval_rescale {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (c : ℚ) (f : PowerSeries ℚ) :
    eval p (PowerSeries.rescale c f) = eval (c • p) f := by
  rw [PowerSeries.rescale_eq_subst,
    eval_subst hp f (c • PowerSeries.X) (by simp)]
  congr 1
  change evalAlgHom hp (c • PowerSeries.X) = c • p
  rw [map_smul, evalAlgHom_apply, eval_X hp]

/-- The exponential addition law along a single formal series. -/
theorem expOf_add_smul {p : PowerSeries A} (hp : p.constantCoeff = 0) (a b : ℚ) :
    expOf ((a + b) • p) = expOf (a • p) * expOf (b • p) := by
  simp only [expOf, ← eval_rescale hp]
  rw [← PowerSeries.exp_mul_exp_eq_exp_add, eval_mul hp]

theorem coeff_expOf (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (expOf p) =
      ∑ k ∈ Finset.range (n + 1), (1 / (k.factorial : ℚ)) •
        PowerSeries.coeff n (p ^ k) := by
  rw [expOf, coeff_eval_eq_sum]
  simp

theorem coeff_logOf (u : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (logOf u) =
      ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then 0 else (-1 : ℚ) ^ (k + 1) / (k : ℚ)) •
          PowerSeries.coeff n ((u - 1) ^ k) := by
  rw [logOf, coeff_eval_eq_sum]
  simp

@[simp] theorem constantCoeff_expOf (p : PowerSeries A) :
    (expOf p).constantCoeff = 1 := by simp [expOf]

@[simp] theorem constantCoeff_logOf (u : PowerSeries A) :
    (logOf u).constantCoeff = 0 := by simp [logOf]

/-- Exponentiation recovers every formal series with constant coefficient one. -/
theorem expOf_logOf {u : PowerSeries A} (hu : u.constantCoeff = 1) :
    expOf (logOf u) = u := by
  have hp : (u - 1).constantCoeff = 0 := by simp [hu]
  have h := eval_subst hp (PowerSeries.exp ℚ) (PowerSeries.log ℚ)
    PowerSeries.constantCoeff_log
  rw [PowerSeries.exp_subst_log, eval_add, eval_one, eval_X hp] at h
  simpa [expOf, logOf] using h.symm

/-- Formal logarithm recovers every series with zero constant coefficient. -/
theorem logOf_expOf {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    logOf (expOf p) = p := by
  have hg : (PowerSeries.exp ℚ - 1).constantCoeff = 0 := by simp
  have h := eval_subst hp (PowerSeries.log ℚ) (PowerSeries.exp ℚ - 1) hg
  rw [PowerSeries.log_subst_exp_sub_one, eval_X hp, eval_sub hp, eval_one] at h
  exact h.symm

/-- The formal exponential is injective on series with zero constant term. -/
theorem expOf_injective {p q : PowerSeries A}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0)
    (h : expOf p = expOf q) : p = q := by
  have h' := congrArg logOf h
  simpa only [logOf_expOf hp, logOf_expOf hq] using h'

/-- The exact exponential identity underlying BCH, for arbitrary
noncommuting coefficient series.  Lie membership is a separate theorem. -/
theorem expOf_logOf_mul_expOf (p q : PowerSeries A)
    (_hp : p.constantCoeff = 0) (_hq : q.constantCoeff = 0) :
    expOf (logOf (expOf p * expOf q)) = expOf p * expOf q :=
  expOf_logOf (by simp)

/-- The formal logarithm of a product of exponentials.  Identifying these
coefficients as Lie polynomials is an additional assertion, not part of this
definition. -/
def bch (p q : PowerSeries A) : PowerSeries A := logOf (expOf p * expOf q)

@[simp] theorem constantCoeff_bch (p q : PowerSeries A) :
    (bch p q).constantCoeff = 0 := by simp [bch]

theorem expOf_bch (p q : PowerSeries A)
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) :
    expOf (bch p q) = expOf p * expOf q := expOf_logOf_mul_expOf p q hp hq

/-- Associativity of the formal exponential product transported through its
formal logarithm.  This is the algebraic identity used in Eichler's and Ha's
proofs of Lie membership. -/
theorem bch_associative (p q r : PowerSeries A)
    (_hp : p.constantCoeff = 0) (_hq : q.constantCoeff = 0)
    (_hr : r.constantCoeff = 0) :
    bch (bch p q) r = bch p (bch q r) := by
  apply expOf_injective (by simp) (by simp)
  simp [bch, expOf_logOf, mul_assoc]

/-- The BCH series on the diagonal has only its linear term. -/
theorem bch_self {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    bch p p = (2 : ℚ) • p := by
  apply expOf_injective (by simp) (by simp [hp])
  rw [expOf_bch p p hp hp]
  simpa only [one_smul, show (1 : ℚ) + 1 = 2 by norm_num] using
    (expOf_add_smul hp 1 1).symm

@[simp] theorem expOf_zero : expOf (0 : PowerSeries A) = 1 := by
  have h := eval_rescale (p := (0 : PowerSeries A)) (by simp) 0 (PowerSeries.exp ℚ)
  simpa [expOf, PowerSeries.rescale_zero] using h.symm

theorem expOf_mul_expOf_neg {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    expOf p * expOf (-p) = 1 := by
  simpa using (expOf_add_smul hp 1 (-1)).symm

theorem expOf_neg_mul_expOf {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    expOf (-p) * expOf p = 1 := by
  simpa using (expOf_add_smul hp (-1) 1).symm

/-- Inverting a product reverses the order of its factors. -/
theorem bch_neg (p q : PowerSeries A)
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) :
    bch (-p) (-q) = -bch q p := by
  apply expOf_injective (by simp) (by simp)
  rw [expOf_bch (-p) (-q) (by simp [hp]) (by simp [hq])]
  have hleft : (expOf (-p) * expOf (-q)) * expOf (bch q p) = 1 := by
    rw [expOf_bch q p hq hp]
    calc
      (expOf (-p) * expOf (-q)) * (expOf q * expOf p) =
          expOf (-p) * (expOf (-q) * expOf q) * expOf p := by simp only [mul_assoc]
      _ = 1 := by rw [expOf_neg_mul_expOf hq, mul_one, expOf_neg_mul_expOf hp]
  calc
    expOf (-p) * expOf (-q) = (expOf (-p) * expOf (-q)) *
        (expOf (bch q p) * expOf (-bch q p)) := by
      rw [expOf_mul_expOf_neg (by simp), mul_one]
    _ = ((expOf (-p) * expOf (-q)) * expOf (bch q p)) * expOf (-bch q p) :=
      (mul_assoc _ _ _).symm
    _ = expOf (-bch q p) := by rw [hleft, one_mul]

end
end AltOMD.NoncommutativeSeries
