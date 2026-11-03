import AltOMD.Algebra.BCHSubstitution
import AltOMD.Algebra.HomogeneousSeries
import AltOMD.Algebra.WordSeries
import AltOMD.Algebra.LieSeries
import AltOMD.Algebra.NoncommutativeBCHTerms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# The formal Baker–Campbell–Hausdorff coefficients are Lie polynomials

The induction uses associativity of formal BCH and its homogeneous expansion.
Modulo the Lie subspace, lower-degree terms vanish after substitution. Comparing
two associations of four inputs gives the four-term identity, from which the
coefficient is Lie by the algebraic criterion in `BCHLieCriterion`.

The four-input induction follows Ha's algebraic proof,
<https://arxiv.org/abs/2608.05053>. All formal-series substitution and Lie-span
steps used by that argument are proved in the imported modules.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators
open DynkinProjection

noncomputable section

variable {ι : Type*}

private abbrev LieQuotient (ι : Type*) :=
  FreeAlgebra ℚ ι ⧸ lieSubmodule (R := ℚ) (ι := ι)

private def lieQuotient : FreeAlgebra ℚ ι →ₗ[ℚ] LieQuotient ι :=
  (lieSubmodule (R := ℚ) (ι := ι)).mkQ

private theorem lieQuotient_eq_zero {a : FreeAlgebra ℚ ι} :
    lieQuotient a = 0 ↔ IsLie a := by
  simp only [lieQuotient, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_lieSubmodule]

private theorem coeff_trunc_eq {p : PowerSeries (FreeAlgebra ℚ ι)}
    {k n : ℕ} (hk : k < n) :
    PowerSeries.coeff k (PowerSeries.trunc n p : PowerSeries (FreeAlgebra ℚ ι)) =
      PowerSeries.coeff k p := by
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk]

private theorem constantCoeff_trunc_eq_zero {p : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (n : ℕ) :
    (PowerSeries.trunc n p : PowerSeries (FreeAlgebra ℚ ι)).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hp]

private theorem bchCoefficient_coeff_congr
    (m n : ℕ) {p q p' q' : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : ∀ k ≤ n, PowerSeries.coeff k p = PowerSeries.coeff k p')
    (hq : ∀ k ≤ n, PowerSeries.coeff k q = PowerSeries.coeff k q') :
    PowerSeries.coeff n (bchCoefficient m p q) =
      PowerSeries.coeff n (bchCoefficient m p' q') := by
  rw [← lift_universalCoefficient, ← lift_universalCoefficient]
  apply WordSeries.coeff_lift_congr
  intro b k hk
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hq k hk | exact hp k hk

/-- Lower-degree universal Lie coefficients imply closure of all lower
coefficients under BCH, including nonlinear series inputs. -/
private theorem isLie_coeff_bch_of_lt {n : ℕ}
    (hIH : ∀ m < n, IsLie (universalCoefficient m))
    {p q : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0)
    (hpL : ∀ k < n, IsLie (PowerSeries.coeff k p))
    (hqL : ∀ k < n, IsLie (PowerSeries.coeff k q))
    {k : ℕ} (hk : k < n) : IsLie (PowerSeries.coeff k (bch p q)) := by
  rw [coeff_bch_eq_sum_bchCoefficient hp hq]
  apply (lieSubmodule (R := ℚ) (ι := ι)).sum_mem
  intro m hm
  have hm' : m < n := by simp only [Finset.mem_range] at hm; omega
  let p' : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.trunc n p
  let q' : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.trunc n q
  have hcoef := bchCoefficient_coeff_congr m k
    (p := p') (q := q') (p' := p) (q' := q)
    (fun j hj => coeff_trunc_eq (by omega)) (fun j hj => coeff_trunc_eq (by omega))
  rw [← hcoef, ← lift_universalCoefficient]
  apply (hIH m hm').lieSeries_lift _ _ k
  intro b
  cases b
  · exact lieSeries_trunc q n hqL
  · exact lieSeries_trunc p n hpL

private theorem isLie_coeff_lower_bchCoefficient {n m : ℕ}
    (hm : 2 ≤ m) (hIH : IsLie (universalCoefficient m))
    {p q : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0)
    (hpL : ∀ k < n, IsLie (PowerSeries.coeff k p))
    (hqL : ∀ k < n, IsLie (PowerSeries.coeff k q)) :
    IsLie (PowerSeries.coeff n (bchCoefficient m p q)) := by
  let p' : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.trunc n p
  let q' : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.trunc n q
  rw [← lift_universalCoefficient]
  have hcoef := WordSeries.coeff_lift_eq_of_lt
    (p := universalCoefficient m)
    (f := fun b : Bool => if b then p else q)
    (g := fun b : Bool => if b then p' else q')
    (n := n) (universalCoefficient_homogeneous m) hm
    (by intro b; cases b <;> assumption)
    (by intro b; cases b <;> exact constantCoeff_trunc_eq_zero (by assumption) n)
    (by intro b k hk; cases b <;> exact (coeff_trunc_eq hk).symm)
  rw [hcoef]
  apply hIH.lieSeries_lift _ _ n
  intro b
  cases b
  · exact lieSeries_trunc q n hqL
  · exact lieSeries_trunc p n hpL

private theorem coeff_bchCoefficient_degree (n : ℕ)
    {p q : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) :
    PowerSeries.coeff n (bchCoefficient n p q) =
      bchCoefficient n (PowerSeries.coeff 1 p) (PowerSeries.coeff 1 q) := by
  rw [← lift_universalCoefficient, ← lift_universalCoefficient]
  simpa only [apply_ite] using WordSeries.coeff_lift_degree
    (p := universalCoefficient n)
    (f := fun b : Bool => if b then p else q)
    (universalCoefficient_homogeneous n) (by intro b; cases b <;> assumption)

private theorem coeff_one_bch {p q : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) :
    PowerSeries.coeff 1 (bch p q) = PowerSeries.coeff 1 p + PowerSeries.coeff 1 q := by
  rw [coeff_bch_eq_sum_bchCoefficient hp hq]
  simp [Finset.sum_range_succ, bchCoefficient_zero, bchCoefficient_one]

/-- Only the linear and top homogeneous terms survive modulo the Lie span. -/
private theorem quotient_coeff_bch {n : ℕ} (hn : 2 < n)
    (hIH : ∀ m < n, IsLie (universalCoefficient m))
    {p q : PowerSeries (FreeAlgebra ℚ ι)}
    (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0)
    (hpL : ∀ k < n, IsLie (PowerSeries.coeff k p))
    (hqL : ∀ k < n, IsLie (PowerSeries.coeff k q)) :
    lieQuotient (PowerSeries.coeff n (bch p q)) =
      lieQuotient (PowerSeries.coeff n p) + lieQuotient (PowerSeries.coeff n q) +
        lieQuotient (bchCoefficient n (PowerSeries.coeff 1 p) (PowerSeries.coeff 1 q)) := by
  rw [coeff_bch_eq_sum_bchCoefficient hp hq, map_sum, Finset.sum_range_succ,
    coeff_bchCoefficient_degree n hp hq]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp only [bchCoefficient_one, map_add]
  · intro m hm hm1
    have hmn : m < n := Finset.mem_range.mp hm
    by_cases hm0 : m = 0
    · subst m; simp [bchCoefficient_zero]
    · exact lieQuotient_eq_zero.mpr
        (isLie_coeff_lower_bchCoefficient (by omega) (hIH m hmn) hp hq hpL hqL)
  · simp [show 1 < n by omega]

private theorem linear_coeff_isLie {a : FreeAlgebra ℚ ι} (ha : IsLie a) (k : ℕ) :
    IsLie (PowerSeries.coeff k (PowerSeries.monomial 1 a)) := by
  rw [PowerSeries.coeff_monomial]
  split_ifs
  · exact ha
  · exact IsLie.zero

/-- Associativity on four linear inputs supplies the four-term defect needed
by the induction; all discarded terms are proved to lie in the Lie subspace. -/
private theorem fourTermDefect_isLie {n : ℕ} (hn : 2 < n)
    (hIH : ∀ m < n, IsLie (universalCoefficient m))
    {a b c d : FreeAlgebra ℚ ι} (ha : IsLie a) (hb : IsLie b)
    (hc : IsLie c) (hd : IsLie d) :
    IsLie (BCHLieCriterion.fourTermDefect (bchCoefficient n) a b c d) := by
  let ta : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.monomial 1 a
  let tb : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.monomial 1 b
  let tc : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.monomial 1 c
  let td : PowerSeries (FreeAlgebra ℚ ι) := PowerSeries.monomial 1 d
  have ha0 : ta.constantCoeff = 0 := by simp [ta]
  have hb0 : tb.constantCoeff = 0 := by simp [tb]
  have hc0 : tc.constantCoeff = 0 := by simp [tc]
  have hd0 : td.constantCoeff = 0 := by simp [td]
  have haL : ∀ k < n, IsLie (PowerSeries.coeff k ta) := fun k _ => linear_coeff_isLie ha k
  have hbL : ∀ k < n, IsLie (PowerSeries.coeff k tb) := fun k _ => linear_coeff_isLie hb k
  have hcL : ∀ k < n, IsLie (PowerSeries.coeff k tc) := fun k _ => linear_coeff_isLie hc k
  have hdL : ∀ k < n, IsLie (PowerSeries.coeff k td) := fun k _ => linear_coeff_isLie hd k
  have habL : ∀ k < n, IsLie (PowerSeries.coeff k (bch ta tb)) :=
    fun _ hk => isLie_coeff_bch_of_lt hIH ha0 hb0 haL hbL hk
  have hcdL : ∀ k < n, IsLie (PowerSeries.coeff k (bch tc td)) :=
    fun _ hk => isLie_coeff_bch_of_lt hIH hc0 hd0 hcL hdL hk
  have hbcL : ∀ k < n, IsLie (PowerSeries.coeff k (bch tb tc)) :=
    fun _ hk => isLie_coeff_bch_of_lt hIH hb0 hc0 hbL hcL hk
  have hbcdL : ∀ k < n, IsLie (PowerSeries.coeff k (bch (bch tb tc) td)) :=
    fun _ hk => isLie_coeff_bch_of_lt hIH (by simp) hd0 hbcL hdL hk
  have hleft := quotient_coeff_bch hn hIH (p := bch ta tb) (q := bch tc td)
    (by simp) (by simp) habL hcdL
  have hright := quotient_coeff_bch hn hIH (p := ta) (q := bch (bch tb tc) td)
    ha0 (by simp) haL hbcdL
  have hinner := quotient_coeff_bch hn hIH (p := bch tb tc) (q := td)
    (by simp) hd0 hbcL hdL
  have hassoc : bch (bch ta tb) (bch tc td) = bch ta (bch (bch tb tc) td) := by
    rw [bch_associative ta tb (bch tc td) ha0 hb0 (by simp),
      bch_associative tb tc td hb0 hc0 hd0]
  have h := congrArg (fun F => lieQuotient (PowerSeries.coeff n F)) hassoc
  rw [hleft, hright, hinner] at h
  simp only [coeff_one_bch ha0 hb0, coeff_one_bch hc0 hd0,
    coeff_one_bch (by simp : (bch tb tc).constantCoeff = 0) hd0,
    coeff_one_bch hb0 hc0] at h
  have hn1 : n ≠ 1 := by omega
  simp only [ta, tb, tc, td, PowerSeries.coeff_monomial, if_neg hn1,
    map_zero, add_zero, zero_add] at h
  change lieQuotient (bchCoefficient n a b) + lieQuotient (bchCoefficient n c d) +
      lieQuotient (bchCoefficient n (a + b) (c + d)) =
    lieQuotient (bchCoefficient n b c) + lieQuotient (bchCoefficient n (b + c) d) +
      lieQuotient (bchCoefficient n a (b + c + d)) at h
  apply lieQuotient_eq_zero.mp
  simp only [BCHLieCriterion.fourTermDefect, map_add, map_sub]
  convert sub_eq_zero.mpr h using 1 <;> abel

/-- Every homogeneous coefficient of the formal BCH logarithm is a Lie
polynomial. This theorem has no external BCH or Lie-membership assumption. -/
theorem universalCoefficient_isLie (n : ℕ) : IsLie (universalCoefficient n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp only [universalCoefficient, bchCoefficient_zero]
      exact IsLie.zero
    by_cases hn1 : n = 1
    · subst n
      simp only [universalCoefficient, bchCoefficient_one]
      exact (IsLie.generator true).add (IsLie.generator false)
    by_cases hn2 : n = 2
    · subst n
      simp only [universalCoefficient, bchCoefficient_two]
      exact IsLie.smul _ ((IsLie.generator true).commutator (IsLie.generator false))
    have hn : 2 < n := by omega
    change bchCoefficient n (FreeAlgebra.ι ℚ true) (FreeAlgebra.ι ℚ false) ∈
      lieSubmodule (R := ℚ) (ι := Bool)
    apply bchCoefficient_mem_of_four_term
      (lieSubmodule (R := ℚ) (ι := Bool)) (lieSubmodule (R := ℚ) (ι := Bool)) n hn
    · intro a ha b hb c hc d hd
      exact fourTermDefect_isLie hn ih ha hb hc hd
    · exact IsLie.generator true
    · exact IsLie.generator false

/-- Evaluating a BCH coefficient on any two Lie polynomials gives a Lie
polynomial, with no homogeneity requirement on the inputs. -/
theorem bchCoefficient_isLie (n : ℕ) {a b : FreeAlgebra ℚ ι}
    (ha : IsLie a) (hb : IsLie b) : IsLie (bchCoefficient n a b) := by
  rw [← lift_universalCoefficient]
  apply (universalCoefficient_isLie n).map
  intro letter
  cases letter <;> assumption


end
end AltOMD.NoncommutativeSeries
