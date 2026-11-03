import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal exponential and logarithm are inverse

These identities concern formal power series, so they require no topology,
norm, or convergence hypothesis.  They are stated for arbitrary commutative
algebras over the rationals, rather than for the particular coefficient
algebra used by the alternating mirror-descent application.
-/

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal derivative of `log(1+X)` is the inverse of `1+X`. -/
theorem deriv_log_mul_one_add_X :
    d⁄dX A (log A) * (1 + X) = 1 := by
  rw [deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have hx : coeff (n + 1)
          ((mk fun k ↦ algebraMap ℚ A ((-1 : ℚ) ^ k)) * X) =
          coeff n (mk fun k ↦ algebraMap ℚ A ((-1 : ℚ) ^ k)) := by
        simpa only [pow_one, Nat.add_comm] using
          coeff_mul_X_pow (mk fun k ↦ algebraMap ℚ A ((-1 : ℚ) ^ k)) 1 n
      rw [map_add, hx]
      simp [coeff_mk, pow_succ]

variable [IsAddTorsionFree A]

/-- `log(exp(X)) = X` as an exact coefficientwise formal-series identity. -/
theorem log_subst_exp_sub_one :
    (log A).subst (exp A - 1) = X := by
  apply derivative.ext
  · rw [derivative_subst HasSubst.exp_sub_one, map_sub, derivative_exp,
      derivative_one, sub_zero, derivative_X]
    have h := congrArg (subst (exp A - 1)) (deriv_log_mul_one_add_X (A := A))
    simpa [subst_mul HasSubst.exp_sub_one, subst_add HasSubst.exp_sub_one,
      subst_X HasSubst.exp_sub_one, ← coe_substAlgHom HasSubst.exp_sub_one] using h
  · rw [constantCoeff_X]
    change constantCoeff (logOf (exp A)) = 0
    exact constantCoeff_logOf constantCoeff_exp

/-- `exp(log(1+X)) = 1+X` as an exact formal-series identity. -/
theorem exp_subst_log : (exp A).subst (log A) = 1 + X := by
  have hL1 : IsUnit (coeff 1 (log A)) := by simp
  obtain ⟨I, hleft⟩ : ∃ I : A⟦X⟧, I.subst (log A) = X :=
    ⟨(log A).substInvOfIsUnit hL1,
      subst_substInvOfIsUnit_left (log A) constantCoeff_log hL1⟩
  have hlog : HasSubst (log A) := HasSubst.log
  have hexp : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  have hE : exp A - 1 = I := by
    calc
      exp A - 1 = (X : A⟦X⟧).subst (exp A - 1) := (subst_X hexp).symm
      _ = PowerSeries.subst (exp A - (1 : A⟦X⟧))
          (PowerSeries.subst (log A) I) := by rw [hleft]
      _ = PowerSeries.subst (PowerSeries.subst (exp A - 1) (log A)) I :=
        subst_comp_subst_apply (R := A) (S := A) (T := A) (υ := Unit)
          (a := log A) (b := (exp A - 1 : PowerSeries A)) hlog hexp I
      _ = I.subst X := by rw [log_subst_exp_sub_one]
      _ = I := X_subst I
  have h := congrArg (subst (log A)) hE
  rw [subst_sub hlog, hleft] at h
  have hone : (1 : A⟦X⟧).subst (log A) = 1 := by
    rw [← coe_substAlgHom hlog, map_one]
  rw [hone] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm X 1)


end PowerSeries
