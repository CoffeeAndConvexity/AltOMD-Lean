import AltOMD.Algebra.FilteredSeries

/-!
# Substitution of positive-order series in the homogeneous BCH coefficients

Summing a filtered double series commutes with formal scalar evaluation and
therefore with formal exponential, logarithm, and BCH. This proves the finite
coefficient expansion for BCH on arbitrary positive-order inputs.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem Admissible.eval {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (f : PowerSeries ℚ) : Admissible (eval F f) := by
  intro m n hnm
  rw [coeff_eval_eq_sum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [PowerSeries.coeff_smul, hF.pow k m n hnm, smul_zero]

theorem diagonal_eval {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hF0 : F.constantCoeff = 0) (f : PowerSeries ℚ) :
    diagonal (eval F f) = eval (diagonal F) f := by
  ext n
  rw [coeff_diagonal, coeff_eval_eq_sum]
  simp_rw [coeff_eval_eq_sum, map_sum, PowerSeries.coeff_smul]
  calc
    _ = ∑ m ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff k f • PowerSeries.coeff n (PowerSeries.coeff m (F ^ k)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_subset (Finset.range_mono (by simpa using hm))
      intro k hk hkm
      have hmk : m < k := by simp only [Finset.mem_range] at hkm; omega
      rw [coeff_pow_eq_zero hF0 hmk, map_zero, smul_zero]
    _ = ∑ k ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff k f • PowerSeries.coeff n (PowerSeries.coeff m (F ^ k)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.smul_sum, ← coeff_diagonal, diagonal_pow hF]

theorem Admissible.expOf {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) : Admissible (expOf F) := hF.eval _

theorem Admissible.logOf {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) : Admissible (logOf F) := (hF.sub Admissible.one).eval _

theorem Admissible.bch {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G) : Admissible (bch F G) :=
  (hF.expOf.mul hG.expOf).logOf

theorem diagonal_expOf {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hF0 : F.constantCoeff = 0) :
    diagonal (expOf F) = expOf (diagonal F) := diagonal_eval hF hF0 _

theorem diagonal_logOf {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hF1 : F.constantCoeff = 1) :
    diagonal (logOf F) = logOf (diagonal F) := by
  unfold logOf
  rw [diagonal_eval (hF.sub Admissible.one) (by simp [hF1]),
    diagonal_sub, diagonal_one]

theorem diagonal_bch {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G)
    (hF0 : F.constantCoeff = 0) (hG0 : G.constantCoeff = 0) :
    diagonal (bch F G) = bch (diagonal F) (diagonal G) := by
  unfold bch
  rw [diagonal_logOf (hF.expOf.mul hG.expOf) (by simp),
    diagonal_mul hF.expOf hG.expOf, diagonal_expOf hF hF0, diagonal_expOf hG hG0]

omit [Algebra ℚ A] in
theorem Admissible.monomial_one {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    Admissible (PowerSeries.monomial 1 p) := by
  intro m n hnm
  rw [PowerSeries.coeff_monomial]
  split_ifs with hm
  · subst m
    have hn : n = 0 := by omega
    simpa only [hn, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hp
  · exact map_zero _

omit [Algebra ℚ A] in
theorem diagonal_monomial_one {p : PowerSeries A} (hp : p.constantCoeff = 0) :
    diagonal (PowerSeries.monomial 1 p) = p := by
  ext n
  rw [coeff_diagonal]
  by_cases hn : n = 0
  · subst n
    simp [PowerSeries.coeff_monomial, hp]
  · simp [PowerSeries.coeff_monomial, apply_ite, show 1 < n + 1 by omega]

/-- The degree-`n` coefficient of BCH after substitution is the finite sum of
the degree-`n` coefficients of its homogeneous BCH polynomials. -/
theorem coeff_bch_eq_sum_bchCoefficient {p q : PowerSeries A}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (bch p q) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (bchCoefficient m p q) := by
  have h := diagonal_bch (Admissible.monomial_one hp) (Admissible.monomial_one hq)
    (constantCoeff_monomial_one p) (constantCoeff_monomial_one q)
  rw [diagonal_monomial_one hp, diagonal_monomial_one hq] at h
  rw [← h, coeff_diagonal]
  rfl

end
end AltOMD.NoncommutativeSeries
