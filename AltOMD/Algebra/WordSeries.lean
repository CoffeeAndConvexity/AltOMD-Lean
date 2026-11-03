import AltOMD.Algebra.DynkinGrading
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.NormNum

/-!
# Homogeneous noncommutative polynomials evaluated in formal series

An ordered word of length `m` in series with zero constant terms has order at
least `m`; its coefficient of degree `m` is the product of the linear terms.
For words of length at least two, a coefficient of degree `n` depends only on
generator coefficients of degrees strictly less than `n`. These statements
extend by linearity to polynomials homogeneous in ordinary word length.
-/

namespace AltOMD.WordSeries

open scoped BigOperators
open PowerSeries DynkinProjection

noncomputable section

variable {ι A : Type*} [Ring A]

/-- The ordered product obtained by replacing the letters of a word by series. -/
def wordSeries (f : ι → PowerSeries A) (w : List ι) : PowerSeries A :=
  (w.map f).prod

@[simp] theorem wordSeries_nil (f : ι → PowerSeries A) : wordSeries f [] = 1 := rfl

@[simp] theorem wordSeries_cons (f : ι → PowerSeries A) (i : ι) (w : List ι) :
    wordSeries f (i :: w) = f i * wordSeries f w := rfl

/-- Positive order of every letter implies the word-length lower bound. -/
theorem wordSeries_order {f : ι → PowerSeries A}
    (hf : ∀ i, (f i).constantCoeff = 0) (w : List ι) :
    (w.length : ℕ∞) ≤ (wordSeries f w).order := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [wordSeries_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        (w.length : ℕ∞) + 1 = 1 + (w.length : ℕ∞) := add_comm _ _
        _ ≤ (f i).order + (wordSeries f w).order :=
          add_le_add (one_le_order_iff_constCoeff_eq_zero.mpr (hf i)) ih
        _ ≤ _ := le_order_mul _ _

theorem coeff_wordSeries_of_lt {f : ι → PowerSeries A}
    (hf : ∀ i, (f i).constantCoeff = 0) {w : List ι} {n : ℕ}
    (hn : n < w.length) : coeff n (wordSeries f w) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hn) (wordSeries_order hf w)

/-- The leading possible coefficient is the ordered product of linear terms. -/
theorem coeff_wordSeries_degree {f : ι → PowerSeries A}
    (hf : ∀ i, (f i).constantCoeff = 0) (w : List ι) :
    coeff w.length (wordSeries f w) = (w.map (fun i => coeff 1 (f i))).prod := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [wordSeries_cons, coeff_mul]
      rw [Finset.sum_eq_single (1, w.length)]
      · simp [ih]
      · rintro ⟨a,b⟩ hab hne
        have hab' : a + b = w.length + 1 := Finset.mem_antidiagonal.mp hab
        by_cases ha : a = 0
        · subst a
          simp [coeff_zero_eq_constantCoeff_apply, hf]
        · have hb : b < w.length := by
            by_contra hb
            have : a = 1 ∧ b = w.length := by omega
            exact hne (Prod.ext this.1 this.2)
          rw [coeff_wordSeries_of_lt hf hb, mul_zero]
      · simp [Nat.add_comm]

/-- Coefficients through degree `n` of the inputs determine the coefficient of
degree `n` of every word, without any assumption on constant terms. -/
theorem coeff_wordSeries_congr {f g : ι → PowerSeries A} {n : ℕ}
    (hfg : ∀ i k, k ≤ n → coeff k (f i) = coeff k (g i)) (w : List ι) :
    coeff n (wordSeries f w) = coeff n (wordSeries g w) := by
  induction w generalizing n with
  | nil => rfl
  | cons i w ih =>
      simp only [wordSeries_cons, coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨a,b⟩ hab
      have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
      rw [hfg i a (by omega), ih (fun i k hk => hfg i k (by omega))]

/-- In a word with at least two positive-order letters, degree `n` depends only
on input degrees strictly below `n`. -/
theorem coeff_wordSeries_eq_of_lt {f g : ι → PowerSeries A} {n : ℕ}
    {w : List ι} (hw : 2 ≤ w.length)
    (hf : ∀ i, (f i).constantCoeff = 0)
    (hg : ∀ i, (g i).constantCoeff = 0)
    (hfg : ∀ i k, k < n → coeff k (f i) = coeff k (g i)) :
    coeff n (wordSeries f w) = coeff n (wordSeries g w) := by
  cases w with
  | nil => simp at hw
  | cons i w =>
      simp only [wordSeries_cons, coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨a,b⟩ hab
      have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
      have hw' : 0 < w.length := by simp only [List.length_cons] at hw; omega
      by_cases ha : a = 0
      · subst a
        simp [coeff_zero_eq_constantCoeff_apply, hf, hg]
      by_cases hb : b = 0
      · subst b
        rw [coeff_wordSeries_of_lt hf hw', coeff_wordSeries_of_lt hg hw']
        simp
      rw [hfg i a (by omega),
        coeff_wordSeries_congr (fun i k hk => hfg i k (by omega))]

section Algebra

variable {R : Type*} [CommRing R] [Algebra R A]

@[simp] theorem lift_word (f : ι → A) (w : List ι) :
    FreeAlgebra.lift R f (word (R := R) w) = (w.map f).prod := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih]

/-- Evaluation of the finite ordinary word expansion. -/
theorem lift_eq_sum_wordCoefficients (f : ι → A) (p : FreeAlgebra R ι) :
    FreeAlgebra.lift R f p = ∑ w ∈ (wordCoefficients p).support,
      wordCoefficients p w • (w.toList.map f).prod := by
  conv_lhs => rw [← sum_wordCoefficients p]
  simp only [Finsupp.sum, map_sum, map_smul, lift_word]

theorem coeff_lift_degree {m : ℕ} {p : FreeAlgebra R ι}
    {f : ι → PowerSeries A} (hp : Homogeneous m p)
    (hf : ∀ i, (f i).constantCoeff = 0) :
    coeff m (FreeAlgebra.lift R f p) =
      FreeAlgebra.lift R (fun i => coeff 1 (f i)) p := by
  classical
  rw [lift_eq_sum_wordCoefficients, lift_eq_sum_wordCoefficients]
  simp only [map_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← homogeneous_iff_support.mp hp w hw]
  exact congrArg (fun a : A => wordCoefficients p w • a)
    (coeff_wordSeries_degree hf w.toList)

theorem coeff_lift_congr {n : ℕ} {p : FreeAlgebra R ι}
    {f g : ι → PowerSeries A}
    (hfg : ∀ i k, k ≤ n → coeff k (f i) = coeff k (g i)) :
    coeff n (FreeAlgebra.lift R f p) = coeff n (FreeAlgebra.lift R g p) := by
  classical
  rw [lift_eq_sum_wordCoefficients, lift_eq_sum_wordCoefficients]
  simp only [map_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro w hw
  exact congrArg (fun a : A => wordCoefficients p w • a)
    (coeff_wordSeries_congr hfg w.toList)

theorem coeff_lift_eq_of_lt {m n : ℕ} {p : FreeAlgebra R ι}
    {f g : ι → PowerSeries A} (hp : Homogeneous m p) (hm : 2 ≤ m)
    (hf : ∀ i, (f i).constantCoeff = 0)
    (hg : ∀ i, (g i).constantCoeff = 0)
    (hfg : ∀ i k, k < n → coeff k (f i) = coeff k (g i)) :
    coeff n (FreeAlgebra.lift R f p) = coeff n (FreeAlgebra.lift R g p) := by
  classical
  rw [lift_eq_sum_wordCoefficients, lift_eq_sum_wordCoefficients]
  simp only [map_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro w hw
  exact congrArg (fun a : A => wordCoefficients p w • a)
    (coeff_wordSeries_eq_of_lt (by rwa [homogeneous_iff_support.mp hp w hw]) hf hg hfg)

end Algebra

end

end AltOMD.WordSeries
