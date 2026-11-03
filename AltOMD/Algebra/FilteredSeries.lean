import AltOMD.Algebra.NoncommutativeRescale

/-!
# Summing a filtered family of noncommutative formal power series

A double series may be summed in its outer variable when its outer degree
bounds the order in the inner variable. Every resulting coefficient is a
finite sum. Polynomial evaluation at one proves the multiplicative law without
commutativity assumptions on the coefficient algebra.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A : Type*} [Ring A]

/-- The inner order is at least the outer degree. -/
def Admissible (F : PowerSeries (PowerSeries A)) : Prop :=
  ∀ m n : ℕ, n < m → PowerSeries.coeff n (PowerSeries.coeff m F) = 0

/-- Sum the outer coefficients; filtration makes each inner coefficient finite. -/
def diagonal (F : PowerSeries (PowerSeries A)) : PowerSeries A :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (PowerSeries.coeff m F)

@[simp] theorem coeff_diagonal (F : PowerSeries (PowerSeries A)) (n : ℕ) :
    PowerSeries.coeff n (diagonal F) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (PowerSeries.coeff m F) :=
  PowerSeries.coeff_mk _ _

theorem Admissible.zero : Admissible (0 : PowerSeries (PowerSeries A)) := by
  intro m n h; simp

theorem Admissible.one : Admissible (1 : PowerSeries (PowerSeries A)) := by
  intro m n h
  rw [PowerSeries.coeff_one, if_neg (by omega : m ≠ 0), map_zero]

theorem Admissible.add {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G) : Admissible (F + G) := by
  intro m n h
  simp only [map_add, hF m n h, hG m n h, add_zero]

theorem Admissible.neg {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) : Admissible (-F) := by
  intro m n h
  simp only [map_neg, hF m n h, neg_zero]

theorem Admissible.sub {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G) : Admissible (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem Admissible.smul [Algebra ℚ A] {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (c : ℚ) : Admissible (c • F) := by
  intro m n h
  simp only [PowerSeries.coeff_smul, hF m n h, smul_zero]

private theorem coeff_convolution_eq_zero
    (f g : ℕ → PowerSeries A)
    (hf : ∀ m n : ℕ, n < m → PowerSeries.coeff n (f m) = 0)
    (hg : ∀ m n : ℕ, n < m → PowerSeries.coeff n (g m) = 0)
    (m n : ℕ) (hn : n < m) :
    PowerSeries.coeff n (∑ ij ∈ Finset.antidiagonal m, f ij.1 * g ij.2) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have hij' := Finset.mem_antidiagonal.mp hij
  have hkl' := Finset.mem_antidiagonal.mp hkl
  by_cases h : kl.1 < ij.1
  · rw [hf _ _ h, zero_mul]
  · rw [hg _ _ (by omega : kl.2 < ij.2), mul_zero]

theorem Admissible.mul {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G) : Admissible (F * G) := by
  intro m n hn
  rw [PowerSeries.coeff_mul]
  exact coeff_convolution_eq_zero _ _ hF hG m n hn

theorem Admissible.pow {F : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (k : ℕ) : Admissible (F ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using Admissible.one (A := A)
  | succ k ih => simpa only [pow_succ] using ih.mul hF

@[simp] theorem diagonal_zero : diagonal (0 : PowerSeries (PowerSeries A)) = 0 := by
  ext n; simp

@[simp] theorem diagonal_add (F G : PowerSeries (PowerSeries A)) :
    diagonal (F + G) = diagonal F + diagonal G := by
  ext n; simp [Finset.sum_add_distrib]

@[simp] theorem diagonal_neg (F : PowerSeries (PowerSeries A)) :
    diagonal (-F) = -diagonal F := by
  ext n; simp

@[simp] theorem diagonal_sub (F G : PowerSeries (PowerSeries A)) :
    diagonal (F - G) = diagonal F - diagonal G := by
  simp only [sub_eq_add_neg, diagonal_add, diagonal_neg]

@[simp] theorem diagonal_smul [Algebra ℚ A] (c : ℚ) (F : PowerSeries (PowerSeries A)) :
    diagonal (c • F) = c • diagonal F := by
  ext n; simp [Finset.smul_sum]

@[simp] theorem diagonal_one : diagonal (1 : PowerSeries (PowerSeries A)) = 1 := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, apply_ite, hn]

theorem coeff_diagonal_of_le {F : PowerSeries (PowerSeries A)} (hF : Admissible F)
    {n N : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (diagonal F) =
      ∑ m ∈ Finset.range (N + 1), PowerSeries.coeff n (PowerSeries.coeff m F) := by
  rw [coeff_diagonal]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro m hm hm'
  exact hF m n (by simp only [Finset.mem_range] at hm'; omega)

private def evalOne : Polynomial (PowerSeries A) →+* PowerSeries A :=
  Polynomial.eval₂RingHom' (RingHom.id _) 1 (fun _ => Commute.one_right _)

private theorem coeff_evalOne_trunc (F : PowerSeries (PowerSeries A)) (n N : ℕ) :
    PowerSeries.coeff n (evalOne (PowerSeries.trunc N F)) =
      ∑ m ∈ Finset.range N, PowerSeries.coeff n (PowerSeries.coeff m F) := by
  change PowerSeries.coeff n
    (Polynomial.eval₂ (RingHom.id _) 1 (PowerSeries.trunc N F)) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply, one_pow, mul_one, map_sum]

private theorem coeff_evalOne_eq_sum (q : Polynomial (PowerSeries A)) (n : ℕ)
    (hq : ∀ m : ℕ, n < m → PowerSeries.coeff n (q.coeff m) = 0) :
    PowerSeries.coeff n (evalOne q) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (q.coeff m) := by
  classical
  change PowerSeries.coeff n (Polynomial.eval 1 q) = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum, map_sum]
  simp only [one_pow, mul_one]
  let s := q.support ∪ Finset.range (n + 1)
  calc
    _ = ∑ m ∈ s, PowerSeries.coeff n (q.coeff m) := by
      apply Finset.sum_subset Finset.subset_union_left
      intro m hm hm'
      rw [Polynomial.notMem_support_iff.mp hm', map_zero]
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro m hm hm'
      exact hq m (by simp only [Finset.mem_range] at hm'; omega)

private theorem trunc_admissible {F : PowerSeries (PowerSeries A)} (hF : Admissible F)
    (N : ℕ) (m n : ℕ) (hn : n < m) :
    PowerSeries.coeff n ((PowerSeries.trunc N F).coeff m) = 0 := by
  rw [PowerSeries.coeff_trunc]
  split_ifs
  · exact hF m n hn
  · exact map_zero _

private theorem coeff_trunc_mul_trunc (F G : PowerSeries (PowerSeries A))
    {m N : ℕ} (hm : m < N) :
    (PowerSeries.trunc N F * PowerSeries.trunc N G).coeff m =
      PowerSeries.coeff m (F * G) := by
  rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc,
    if_pos (by omega : ij.1 < N), if_pos (by omega : ij.2 < N)]

/-- Summing a filtered double series respects multiplication. -/
theorem diagonal_mul {F G : PowerSeries (PowerSeries A)}
    (hF : Admissible F) (hG : Admissible G) :
    diagonal (F * G) = diagonal F * diagonal G := by
  ext n
  calc
    _ = PowerSeries.coeff n
        (evalOne (PowerSeries.trunc (n + 1) F * PowerSeries.trunc (n + 1) G)) := by
      rw [coeff_diagonal, coeff_evalOne_eq_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [coeff_trunc_mul_trunc F G (Finset.mem_range.mp hm)]
      · intro m hm
        rw [Polynomial.coeff_mul]
        exact coeff_convolution_eq_zero _ _ (trunc_admissible hF _)
          (trunc_admissible hG _) m n hm
    _ = PowerSeries.coeff n
        (evalOne (PowerSeries.trunc (n + 1) F) *
          evalOne (PowerSeries.trunc (n + 1) G)) := by rw [map_mul]
    _ = _ := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      rw [coeff_evalOne_trunc, coeff_evalOne_trunc,
        coeff_diagonal_of_le hF (by omega : ij.1 ≤ n),
        coeff_diagonal_of_le hG (by omega : ij.2 ≤ n)]

theorem diagonal_pow {F : PowerSeries (PowerSeries A)} (hF : Admissible F) (k : ℕ) :
    diagonal (F ^ k) = diagonal F ^ k := by
  induction k with
  | zero => simp only [pow_zero, diagonal_one]
  | succ k ih => rw [pow_succ, diagonal_mul (hF.pow k) hF, ih, pow_succ]

end
end AltOMD.NoncommutativeSeries
