import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.NormNum

/-!
# Scalar power series evaluated in a noncommutative coefficient algebra

The variable of a scalar formal power series may be replaced by a series of
positive order even when its coefficients belong to a noncommutative algebra.
Every coefficient is a finite sum.  Polynomial truncation makes the algebra
laws independent of any convergence or completeness assumption.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators
open PowerSeries

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Evaluate a scalar power series coefficientwise at a positive-order series.
The condition of positive order is required by the algebra laws below. -/
def eval (p : PowerSeries A) (f : PowerSeries ℚ) : PowerSeries A :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n (Polynomial.aeval p (PowerSeries.trunc (n + 1) f))

@[simp] theorem coeff_eval (p : PowerSeries A) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (eval p f) =
      PowerSeries.coeff n (Polynomial.aeval p (PowerSeries.trunc (n + 1) f)) :=
  PowerSeries.coeff_mk _ _

omit [Algebra ℚ A] in
theorem coeff_pow_eq_zero {p : PowerSeries A} (hp : p.constantCoeff = 0)
    {n k : ℕ} (hn : n < k) : PowerSeries.coeff n (p ^ k) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hn)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hp)

theorem coeff_eval_eq_sum (p : PowerSeries A) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (eval p f) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f • PowerSeries.coeff n (p ^ k) := by
  rw [coeff_eval, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [map_sum, ← Algebra.smul_def, PowerSeries.coeff_smul]

private theorem trunc_polynomial_monomial (n k : ℕ) (c : ℚ) :
    PowerSeries.trunc (n + 1) (Polynomial.monomial k c : PowerSeries ℚ) =
      if k ≤ n then Polynomial.monomial k c else 0 := by
  ext j
  by_cases hj : j = k
  · subst j
    by_cases hk : k ≤ n <;> simp [PowerSeries.coeff_trunc, hk]
  · by_cases hk : k ≤ n <;>
      simp [PowerSeries.coeff_trunc, PowerSeries.coeff_monomial,
        Polynomial.coeff_monomial, hj, Ne.symm hj, hk]

theorem coeff_aeval_trunc {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (q : Polynomial ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (Polynomial.aeval p (PowerSeries.trunc (n + 1) (q : PowerSeries ℚ))) =
      PowerSeries.coeff n (Polynomial.aeval p q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simpa only [map_add, Polynomial.coe_add] using congrArg₂ (· + ·) hq hr
  | monomial k c =>
    rw [trunc_polynomial_monomial]
    split_ifs with hk
    · rfl
    · simp only [map_zero, Polynomial.aeval_def, Polynomial.eval₂_monomial,
        ← Algebra.smul_def, PowerSeries.coeff_smul,
        coeff_pow_eq_zero hp (by omega : n < k), smul_zero]

/-- Coefficients through `n` can be computed using any truncation beyond `n`. -/
theorem coeff_eval_of_le {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f : PowerSeries ℚ) {n N : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (eval p f) =
      PowerSeries.coeff n (Polynomial.aeval p (PowerSeries.trunc (N + 1) f)) := by
  calc
    _ = PowerSeries.coeff n (Polynomial.aeval p
        (PowerSeries.trunc (n + 1) (PowerSeries.trunc (N + 1) f : PowerSeries ℚ))) := by
      rw [PowerSeries.trunc_trunc_of_le f (Nat.add_le_add_right hn 1)]
      exact coeff_eval p f n
    _ = _ := coeff_aeval_trunc hp _ n

@[simp] theorem eval_zero (p : PowerSeries A) : eval p 0 = 0 := by
  ext n
  simp

@[simp] theorem eval_add (p : PowerSeries A) (f g : PowerSeries ℚ) :
    eval p (f + g) = eval p f + eval p g := by
  ext n
  simp

@[simp] theorem eval_one (p : PowerSeries A) : eval p 1 = 1 := by
  ext n
  simp

@[simp] theorem eval_C (p : PowerSeries A) (c : ℚ) :
    eval p (PowerSeries.C c) = algebraMap ℚ (PowerSeries A) c := by
  ext n
  simp

@[simp] theorem eval_polynomial {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (q : Polynomial ℚ) : eval p (q : PowerSeries ℚ) = Polynomial.aeval p q := by
  ext n
  rw [coeff_eval]
  exact coeff_aeval_trunc hp q n

@[simp] theorem eval_X {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    eval p (PowerSeries.X : PowerSeries ℚ) = p := by
  rw [← Polynomial.coe_X, eval_polynomial hp, Polynomial.aeval_X]

theorem eval_mul {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f g : PowerSeries ℚ) : eval p (f * g) = eval p f * eval p g := by
  ext n
  calc
    PowerSeries.coeff n (eval p (f * g)) =
        PowerSeries.coeff n (Polynomial.aeval p
          (PowerSeries.trunc (n + 1) f * PowerSeries.trunc (n + 1) g)) := by
      rw [coeff_eval, ← PowerSeries.trunc_trunc_mul_trunc f g,
        ← Polynomial.coe_mul, coeff_aeval_trunc hp]
    _ = PowerSeries.coeff n
        (Polynomial.aeval p (PowerSeries.trunc (n + 1) f) *
          Polynomial.aeval p (PowerSeries.trunc (n + 1) g)) := by rw [map_mul]
    _ = PowerSeries.coeff n (eval p f * eval p g) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      rw [coeff_eval_of_le hp f (by omega : ij.1 ≤ n),
        coeff_eval_of_le hp g (by omega : ij.2 ≤ n)]

/-- Scalar substitution into a positive-order series is an algebra homomorphism,
without commutativity of the target coefficient ring. -/
def evalAlgHom {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    PowerSeries ℚ →ₐ[ℚ] PowerSeries A where
  toFun := eval p
  map_zero' := eval_zero p
  map_add' := eval_add p
  map_one' := eval_one p
  map_mul' := eval_mul hp
  commutes' c := by simp

@[simp] theorem evalAlgHom_apply {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f : PowerSeries ℚ) : evalAlgHom hp f = eval p f := rfl

@[simp] theorem eval_sub {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f g : PowerSeries ℚ) : eval p (f - g) = eval p f - eval p g :=
  map_sub (evalAlgHom hp) f g

@[simp] theorem eval_pow {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f : PowerSeries ℚ) (n : ℕ) : eval p (f ^ n) = eval p f ^ n :=
  map_pow (evalAlgHom hp) f n

theorem coeff_eval_congr (p : PowerSeries A) {f g : PowerSeries ℚ} (n : ℕ)
    (h : ∀ k ≤ n, PowerSeries.coeff k f = PowerSeries.coeff k g) :
    PowerSeries.coeff n (eval p f) = PowerSeries.coeff n (eval p g) := by
  rw [coeff_eval_eq_sum, coeff_eval_eq_sum]
  exact Finset.sum_congr rfl fun k hk => by rw [h k (by simpa using hk)]

@[simp] theorem constantCoeff_eval (p : PowerSeries A) (f : PowerSeries ℚ) :
    (eval p f).constantCoeff = algebraMap ℚ A f.constantCoeff := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_eval_eq_sum]
  simp [Algebra.algebraMap_eq_smul_one]

theorem eval_aeval {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (g : PowerSeries ℚ) (q : Polynomial ℚ) :
    eval p (Polynomial.aeval g q) = Polynomial.aeval (eval p g) q := by
  have h : (evalAlgHom hp).comp (Polynomial.aeval g) =
      Polynomial.aeval (eval p g) := Polynomial.algHom_ext (by simp)
  exact AlgHom.congr_fun h q

private theorem coeff_subst_trunc (f g : PowerSeries ℚ)
    (hg : g.constantCoeff = 0) (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (f.subst g) =
      PowerSeries.coeff n ((PowerSeries.trunc (N + 1) f : PowerSeries ℚ).subst g) := by
  have hgs := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [PowerSeries.coeff_subst' hgs, PowerSeries.coeff_subst' hgs]
  apply finsum_congr
  intro k
  by_cases hk : k ≤ N
  · simp [PowerSeries.coeff_trunc, hk]
  · rw [coeff_pow_eq_zero hg (by omega : n < k)]
    simp

/-- Composition of scalar power series remains valid after evaluation in a
noncommutative coefficient ring. -/
theorem eval_subst {p : PowerSeries A} (hp : p.constantCoeff = 0)
    (f g : PowerSeries ℚ) (hg : g.constantCoeff = 0) :
    eval p (f.subst g) = eval (eval p g) f := by
  ext n
  calc
    PowerSeries.coeff n (eval p (f.subst g)) =
        PowerSeries.coeff n
          (eval p ((PowerSeries.trunc (n + 1) f : PowerSeries ℚ).subst g)) :=
      coeff_eval_congr p n fun k hk => coeff_subst_trunc f g hg n hk
    _ = PowerSeries.coeff n
        (Polynomial.aeval (eval p g) (PowerSeries.trunc (n + 1) f)) := by
      rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hg), eval_aeval hp]
    _ = PowerSeries.coeff n (eval (eval p g) f) := (coeff_eval _ _ _).symm

end
end AltOMD.NoncommutativeSeries
