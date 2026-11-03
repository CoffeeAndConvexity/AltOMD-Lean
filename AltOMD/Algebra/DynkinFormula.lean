import AltOMD.Algebra.BCHLie
import AltOMD.Algebra.CompositionCoefficients
import AltOMD.Algebra.DynkinGrading

/-!
# The rational explicit Dynkin formula

A composition records the positive block lengths `r_i + s_i`. Each block
is split at every `r_i = 0, ..., r_i + s_i`, with coefficient
`1 / (r_i! s_i!)`. The list `blockProducts` retains every such choice, before
equal words are collected. Thus `explicitCoefficient` is the finite rational
right-nested-commutator formula in Proposition A.1, indexed by compositions
instead of a separate number of blocks and a total-degree constraint.
-/

namespace AltOMD.DynkinFormula

open scoped BigOperators
open NoncommutativeSeries

noncomputable section

abbrev Word := List Bool
abbrev Polynomial := List (ℚ × Word)

/-- All splits `r + s = n`, in the order `U^r V^s`. -/
def blockTerms (n : ℕ) : Polynomial :=
  (Finset.range (n + 1)).toList.map fun r =>
    (1 / ((r.factorial : ℚ) * ((n - r).factorial : ℚ)),
      List.replicate r true ++ List.replicate (n - r) false)

def prepend (a : ℚ) (w : Word) (p : Polynomial) : Polynomial :=
  p.map fun t => (a * t.1, w ++ t.2)

def multiply : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | (a, w) :: p, q => prepend a w q ++ multiply p q

/-- Every choice of a split in each block, with its product of factorial
denominators and its concatenated word. -/
def blockProducts : List ℕ → Polynomial
  | [] => [(1, [])]
  | n :: ns => multiply (blockTerms n) (blockProducts ns)

def evaluate : Polynomial → FreeAlgebra ℚ Bool
  | [] => 0
  | (a, w) :: p => a • DynkinProjection.word w + evaluate p

/-- The explicit sum of rational multiples of right-nested commutators. -/
def evaluateNested (p : Polynomial) : FreeAlgebra ℚ Bool :=
  (p.map fun t => t.1 • DynkinProjection.nested t.2).sum

/-- The homogeneous degree-`q` Dynkin formula. The length of a composition
is the number `m` of blocks in the manuscript's formula. For positive `q`,
also `m > 0`, so `(-1)^(m+1) = (-1)^(m-1)`. -/
def explicitCoefficient (q : ℕ) : FreeAlgebra ℚ Bool :=
  (1 / (q : ℚ)) • ∑ c : Composition q,
    ((-1 : ℚ) ^ (c.length + 1) / (c.length : ℚ)) •
      evaluateNested (blockProducts c.blocks)

private theorem evaluate_append (p q : Polynomial) :
    evaluate (p ++ q) = evaluate p + evaluate q := by
  induction p with
  | nil => simp [evaluate]
  | cons t p ih => simp [evaluate, ih, add_assoc]

private theorem word_append (w v : Word) :
    DynkinProjection.word (R := ℚ) (w ++ v) =
      DynkinProjection.word w * DynkinProjection.word v := by
  simp [DynkinProjection.word]

private theorem evaluate_prepend (a : ℚ) (w : Word) (p : Polynomial) :
    evaluate (prepend a w p) = (a • DynkinProjection.word w) * evaluate p := by
  induction p with
  | nil => simp [prepend, evaluate]
  | cons t p ih =>
      change (a * t.1) • DynkinProjection.word (w ++ t.2) +
        evaluate (prepend a w p) =
          (a • DynkinProjection.word w) *
            (t.1 • DynkinProjection.word t.2 + evaluate p)
      rw [ih]
      simp [mul_add, smul_smul, mul_comm a t.1]

private theorem evaluate_multiply (p q : Polynomial) :
    evaluate (multiply p q) = evaluate p * evaluate q := by
  induction p with
  | nil => simp [multiply, evaluate]
  | cons t p ih => simp [multiply, evaluate, evaluate_append, evaluate_prepend, ih, add_mul]

private theorem evaluate_map {ι : Type*} (l : List ι) (f : ι → ℚ × Word) :
    evaluate (l.map f) =
      (l.map fun i => (f i).1 • DynkinProjection.word (f i).2).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [evaluate, ih]

private theorem evaluate_blockTerms (n : ℕ) :
    evaluate (blockTerms n) =
      ∑ r ∈ Finset.range (n + 1),
        (1 / ((r.factorial : ℚ) * ((n - r).factorial : ℚ))) •
          ((FreeAlgebra.ι ℚ true) ^ r * (FreeAlgebra.ι ℚ false) ^ (n - r)) := by
  rw [blockTerms, evaluate_map]
  simp [DynkinProjection.word]

private theorem evaluate_blockProducts (ns : List ℕ) :
    evaluate (blockProducts ns) = (ns.map fun n => evaluate (blockTerms n)).prod := by
  induction ns with
  | nil => simp [blockProducts, evaluate, DynkinProjection.word]
  | cons n ns ih => simp [blockProducts, evaluate_multiply, ih]

private theorem dynkin_evaluate (p : Polynomial) :
    DynkinProjection.dynkin (evaluate p) = evaluateNested p := by
  induction p with
  | nil => simp [evaluate, evaluateNested]
  | cons t p ih =>
      simp [evaluate, evaluateNested, map_add, map_smul,
        DynkinProjection.dynkin_word, ih]

section Series

variable {A : Type*} [Ring A] [Algebra ℚ A]

omit [Algebra ℚ A] in
private theorem monomial_one_pow (a : A) (n : ℕ) :
    (PowerSeries.monomial 1 a) ^ n = PowerSeries.monomial n (a ^ n) := by
  induction n with
  | zero => simp [PowerSeries.monomial_zero_eq_C_apply]
  | succ n ih => rw [pow_succ, ih, PowerSeries.monomial_mul_monomial, pow_succ]

private theorem coeff_exp_linear (a : A) (n : ℕ) :
    PowerSeries.coeff n (expOf (PowerSeries.monomial 1 a)) =
      (1 / (n.factorial : ℚ)) • a ^ n := by
  rw [coeff_expOf]
  simp only [monomial_one_pow, PowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    simp [Ne.symm hkn]
  · simp

end Series

private def splitSeries : PowerSeries (FreeAlgebra ℚ Bool) :=
  expOf (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ true)) *
    expOf (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ false))

private theorem coeff_splitSeries (n : ℕ) :
    PowerSeries.coeff n splitSeries = evaluate (blockTerms n) := by
  rw [splitSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, evaluate_blockTerms]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coeff_exp_linear, coeff_exp_linear]
  simp [smul_smul]

/-- The explicit associative block expansion, before Dynkin projection. -/
theorem universalCoefficient_eq_blocks (q : ℕ) :
    universalCoefficient q = ∑ c : Composition q,
      ((-1 : ℚ) ^ (c.length + 1) / (c.length : ℚ)) •
        evaluate (blockProducts c.blocks) := by
  have hp : (splitSeries - 1).constantCoeff = 0 := by simp [splitSeries]
  change PowerSeries.coeff q (logOf splitSeries) = _
  rw [coeff_logOf, CompositionCoefficients.weighted_coeff_pow_sum _ hp]
  apply Finset.sum_congr rfl
  intro c hc
  rw [evaluate_blockProducts]
  have hcoeff :
      (c.blocks.map fun j => PowerSeries.coeff j (splitSeries - 1)).prod =
        (c.blocks.map fun j => evaluate (blockTerms j)).prod := by
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj0 : j ≠ 0 := Nat.ne_of_gt (c.blocks_pos hj)
    simp [PowerSeries.coeff_one, hj0, coeff_splitSeries]
  rw [hcoeff]
  by_cases hk : c.length = 0 <;> simp [hk]

/-- Dynkin's explicit rational formula for every positive homogeneous degree.
No convergence or unproved BCH/DSW hypothesis is required. -/
theorem universalCoefficient_eq_dynkin (q : ℕ) (hq : 0 < q) :
    universalCoefficient q = explicitCoefficient q := by
  have hproj := DynkinProjection.inv_degree_smul_dynkin_of_isLie
    (K := ℚ) (n := q) (by exact_mod_cast (Nat.ne_of_gt hq))
    (universalCoefficient_isLie q) (universalCoefficient_homogeneous q)
  rw [← hproj, universalCoefficient_eq_blocks, map_sum]
  simp only [map_smul, dynkin_evaluate, explicitCoefficient, one_div]

end
end AltOMD.DynkinFormula
