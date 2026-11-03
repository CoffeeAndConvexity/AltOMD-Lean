import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The four-term algebraic criterion for BCH Lie membership

This is the final algebraic step of Eugene Ha's variation of Eichler's proof:
<https://arxiv.org/html/2608.05053v1>, Section 1.

The theorem is deliberately stated with its hypotheses visible: it does not
prove that the coefficients of a formal logarithm satisfy the four-term
condition. That remaining formal-series argument is needed before applying
the criterion to BCH. Here the submodule can be the space of Lie polynomials,
but the algebraic criterion works for any submodule.
-/

namespace AltOMD.BCHLieCriterion

variable {A : Type*} [AddCommGroup A] [Module ℚ A]

/-- The degree-`n` defect obtained by comparing two associations of four
exponentials. For BCH, lower-degree Lie membership implies that this defect
belongs to the submodule of Lie polynomials. -/
def fourTermDefect (h : A → A → A) (a b c d : A) : A :=
  h a b + h c d + h (a + b) (c + d) - h b c - h (b + c) d - h a (b + c + d)

theorem coefficient_pos (n : ℕ) (hn : 2 < n) :
    (0 : ℚ) < 2 ^ n - (-1) ^ n - 3 := by
  have hpow : (8 : ℚ) ≤ 2 ^ n := by
    calc
      (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hsign : (-1 : ℚ) ^ n ≤ 1 := by
    have habs : |(-1 : ℚ) ^ n| = 1 := by simp
    exact (le_abs_self _).trans habs.le
  linarith

/-- Ha's two substitutions force membership in any submodule. All input
conditions are exact equalities or submodule membership statements. -/
theorem mem_of_four_term (S W : Submodule ℚ A) (h : A → A → A)
    (n : ℕ) (hn : 2 < n)
    (hdiag : ∀ a ∈ W, h a a = 0)
    (hscale : ∀ a ∈ W, ∀ b ∈ W,
      h ((2 : ℚ) • a) ((2 : ℚ) • b) = (2 ^ n : ℚ) • h a b)
    (hswap : ∀ a ∈ W, ∀ b ∈ W,
      h b a = -((-1 : ℚ) ^ n • h a b))
    (hfour : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W,
      fourTermDefect h a b c d ∈ S)
    {x y : A} (hx : x ∈ W) (hy : y ∈ W) : h x y ∈ S := by
  have hm := S.sub_mem (hfour x hx x hx y hy y hy)
    (hfour x hx y hy x hx y hy)
  have hscale' := hscale x hx y hy
  simp only [two_smul ℚ] at hscale'
  have hid : fourTermDefect h x x y y - fourTermDefect h x y x y =
      (2 ^ n - (-1) ^ n - 3 : ℚ) • h x y := by
    unfold fourTermDefect
    rw [hdiag x hx, hdiag y hy, hdiag (x + y) (W.add_mem hx hy), hscale',
      hswap x hx y hy]
    simp only [add_comm y x, add_assoc]
    module
  rw [hid] at hm
  have hc : (2 ^ n - (-1) ^ n - 3 : ℚ) ≠ 0 := ne_of_gt (coefficient_pos n hn)
  have := S.smul_mem (2 ^ n - (-1) ^ n - 3 : ℚ)⁻¹ hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using this

end AltOMD.BCHLieCriterion
