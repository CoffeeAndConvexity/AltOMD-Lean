import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Ordered coefficient expansions indexed by compositions

For a formal power series with zero constant term, the coefficient of its
`k`th power is a sum over compositions with `k` blocks. Products are list
products in their original order, so the coefficient ring need not commute.
-/

namespace AltOMD.CompositionCoefficients

open scoped BigOperators

noncomputable section

private def prepend (n : ℕ) (j : Fin (n + 1)) (c : Composition (n - j)) :
    Composition (n + 1) where
  blocks := (j.val + 1) :: c.blocks
  blocks_pos := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact c.blocks_pos ha
  blocks_sum := by
    simp only [List.sum_cons, c.blocks_sum]
    have := j.isLt
    omega

private def split (n : ℕ) (c : Composition (n + 1)) :
    Σ j : Fin (n + 1), Composition (n - j) := by
  rcases c with ⟨l, hpos, hsum⟩
  cases l with
  | nil => simp at hsum
  | cons a l =>
      cases a with
      | zero => have := hpos (by simp : 0 ∈ 0 :: l); omega
      | succ j =>
          have hsum' : j + 1 + l.sum = n + 1 := hsum
          refine ⟨⟨j, by omega⟩, ⟨l, ?_, ?_⟩⟩
          · intro a ha
            exact hpos (List.mem_cons_of_mem _ ha)
          · change l.sum = n - j
            omega

/-- A nonempty composition is uniquely its positive first block and the
composition formed by the remaining blocks. -/
def headTailEquiv (n : ℕ) : Composition (n + 1) ≃
    (Σ j : Fin (n + 1), Composition (n - j)) where
  toFun := split n
  invFun x := prepend n x.1 x.2
  left_inv c := by
    rcases c with ⟨l, hpos, hsum⟩
    cases l with
    | nil => simp at hsum
    | cons a l =>
        cases a with
        | zero => have := hpos (by simp : 0 ∈ 0 :: l); omega
        | succ j => apply Composition.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨j, hj⟩, ⟨l, hpos, hsum⟩⟩
    rfl

@[simp] theorem headTailEquiv_symm_blocks (n : ℕ) (j : Fin (n + 1))
    (c : Composition (n - j)) :
    ((headTailEquiv n).symm ⟨j, c⟩).blocks = (j.val + 1) :: c.blocks := rfl

@[simp] theorem headTailEquiv_symm_length (n : ℕ) (j : Fin (n + 1))
    (c : Composition (n - j)) :
    ((headTailEquiv n).symm ⟨j, c⟩).length = c.length + 1 := rfl

private theorem composition_zero_unique (c : Composition 0) : c = Composition.ones 0 := by
  apply Composition.ext
  simp

private instance compositionZeroUnique : Unique (Composition 0) where
  default := Composition.ones 0
  uniq := composition_zero_unique

variable {A : Type*} [Semiring A]

/-- Ordered products of coefficients with a prescribed number of positive blocks. -/
def blockCoefficient (p : PowerSeries A) (n k : ℕ) : A :=
  ∑ c : Composition n, if c.length = k then
    (c.blocks.map (fun j => PowerSeries.coeff j p)).prod else 0

@[simp] theorem blockCoefficient_zero_degree (p : PowerSeries A) (k : ℕ) :
    blockCoefficient p 0 k = if k = 0 then 1 else 0 := by
  simp [blockCoefficient, eq_comm,
    show (default : Composition 0) = Composition.ones 0 from composition_zero_unique _]

@[simp] theorem blockCoefficient_zero_power (p : PowerSeries A) (n : ℕ) :
    blockCoefficient p n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
      simp [blockCoefficient]

/-- Splitting off the first block preserves the order of the product. -/
theorem blockCoefficient_succ (p : PowerSeries A) (n k : ℕ) :
    blockCoefficient p (n + 1) (k + 1) =
      ∑ j : Fin (n + 1), PowerSeries.coeff (j.val + 1) p *
        blockCoefficient p (n - j.val) k := by
  unfold blockCoefficient
  rw [← (headTailEquiv n).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [headTailEquiv_symm_length, Nat.add_right_cancel_iff,
    headTailEquiv_symm_blocks, List.map_cons, List.prod_cons]
  split_ifs <;> simp_all

/-- The coefficient of a power of a positive-order series, with no commutativity
assumption on the coefficient semiring. -/
theorem coeff_pow_eq_blockCoefficient (p : PowerSeries A)
    (hp : p.constantCoeff = 0) (k n : ℕ) :
    PowerSeries.coeff n (p ^ k) = blockCoefficient p n k := by
  induction k generalizing n with
  | zero => simp [PowerSeries.coeff_one]
  | succ k ih =>
      cases n with
      | zero =>
          rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hp]
          simp
      | succ n =>
          rw [pow_succ', PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
            Finset.sum_range_succ']
          simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, zero_mul, add_zero]
          rw [blockCoefficient_succ, Finset.sum_range]
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih]
          congr 2
          omega

/-- Explicit composition form of the noncommutative coefficient formula. -/
theorem coeff_pow_eq_sum_compositions (p : PowerSeries A)
    (hp : p.constantCoeff = 0) (k n : ℕ) :
    PowerSeries.coeff n (p ^ k) =
      ∑ c : Composition n, if c.length = k then
        (c.blocks.map (fun j => PowerSeries.coeff j p)).prod else 0 :=
  coeff_pow_eq_blockCoefficient p hp k n

/-- A finite weighted sum over powers is equivalently one sum over all
compositions; the weight is evaluated at the number of blocks. -/
theorem weighted_coeff_pow_sum {R : Type*} [Semiring R] [Module R A]
    (p : PowerSeries A) (hp : p.constantCoeff = 0) (weight : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), weight k • PowerSeries.coeff n (p ^ k)) =
      ∑ c : Composition n, weight c.length •
        (c.blocks.map (fun j => PowerSeries.coeff j p)).prod := by
  simp_rw [coeff_pow_eq_blockCoefficient p hp, blockCoefficient, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [c.length_le]

end

end AltOMD.CompositionCoefficients
