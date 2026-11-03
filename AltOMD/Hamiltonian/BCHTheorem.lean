import AltOMD.Hamiltonian.BCHCoefficients
import AltOMD.Hamiltonian.BCHLogarithm
import AltOMD.Hamiltonian.SeriesAction
import AltOMD.Algebra.DynkinGrading
import AltOMD.Algebra.NoncommutativeMap
import AltOMD.BCH

/-!
# Application of Proposition A.1 to the canonical Lie expressions

Ordinary word homogeneity, proved universal Lie membership, and the
Dynkin–Specht–Wever identity identify the canonical nested coefficients.
The universal proposition is exposed by `AltOMD.BCH`. This adapter proves
the operator exponential identity for the same canonical sequence whose
Hamiltonian representation is established in `BCHCoefficients`.
No external BCH, DSW, or Lie-membership premise is required.
-/

namespace AltOMD.BCHTheorem

open scoped BigOperators
open WordCoefficients FormalEnergy

noncomputable section

local instance : Algebra ℚ (FreeAlgebra ℝ Bool) :=
  Algebra.compHom (FreeAlgebra ℝ Bool) (algebraMap ℚ ℝ)

/-- Interpret the uncollected real word polynomial in the free real algebra. -/
def freeEvaluate (p : WordCoefficients.Polynomial) : FreeAlgebra ℝ Bool :=
  evaluate (FreeAlgebra.ι ℝ true) (FreeAlgebra.ι ℝ false) p

theorem evaluateWord_free (w : Word) :
    evaluateWord (FreeAlgebra.ι ℝ true) (FreeAlgebra.ι ℝ false) w =
      DynkinProjection.word (R := ℝ) w := by
  unfold evaluateWord DynkinProjection.word
  congr 1
  apply List.map_congr_left
  intro b hb
  cases b <;> rfl

theorem freeEvaluate_homogeneous (n : ℕ) (p : WordCoefficients.Polynomial)
    (hp : WordCoefficients.Homogeneous n p) :
    DynkinProjection.Homogeneous n (freeEvaluate p) := by
  revert hp
  induction p with
  | nil => intro hp; exact DynkinProjection.Homogeneous.zero n
  | cons t p ih =>
      intro hp
      change DynkinProjection.Homogeneous n
        (t.1 • evaluateWord (FreeAlgebra.ι ℝ true) (FreeAlgebra.ι ℝ false) t.2 +
          freeEvaluate p)
      rw [evaluateWord_free]
      apply DynkinProjection.Homogeneous.add
      · have ht : t.2.length = n := hp t (by simp)
        simpa only [ht] using (DynkinProjection.homogeneous_word (R := ℝ) t.2).smul t.1
      · exact ih fun u hu => hp u (by simp [hu])

private def scalarExtension : FreeAlgebra ℚ Bool →ₐ[ℚ] FreeAlgebra ℝ Bool :=
  FreeAlgebra.lift ℚ (FreeAlgebra.ι ℝ)

private theorem scalarExtension_isLie {p : FreeAlgebra ℚ Bool}
    (hp : DynkinProjection.IsLie p) : DynkinProjection.IsLie (scalarExtension p) := by
  induction hp with
  | zero => simpa using (DynkinProjection.IsLie.zero (R := ℝ) (ι := Bool))
  | generator i =>
      simpa [scalarExtension] using (DynkinProjection.IsLie.generator (R := ℝ) i)
  | add hp hq ihp ihq => simpa using DynkinProjection.IsLie.add ihp ihq
  | smul r hp ih =>
      have h := DynkinProjection.IsLie.smul (r : ℝ) ih
      rw [← map_ratCast_smul scalarExtension ℚ ℝ r] at h
      simpa using h
  | commutator hp hq ihp ihq =>
      simpa using DynkinProjection.IsLie.commutator ihp ihq

theorem scalarExtension_universalCoefficient (n : ℕ) :
    scalarExtension (NoncommutativeSeries.universalCoefficient n) =
      freeEvaluate (logarithm n) := by
  rw [NoncommutativeSeries.universalCoefficient,
    NoncommutativeSeries.map_bchCoefficient]
  simp only [scalarExtension, FreeAlgebra.lift_ι_apply]
  exact BCHLogarithm.coeff_bch_monomial_one _ _ n

theorem freeEvaluate_logarithm_isLie (n : ℕ)
    (hn : DynkinProjection.IsLie (NoncommutativeSeries.universalCoefficient n)) :
    DynkinProjection.IsLie (freeEvaluate (logarithm n)) := by
  rw [← scalarExtension_universalCoefficient]
  exact scalarExtension_isLie hn

section Evaluation

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem lift_word (f : Bool → A) (w : Word) :
    FreeAlgebra.lift ℝ f (DynkinProjection.word (R := ℝ) w) = (w.map f).prod := by
  induction w with
  | nil => simp
  | cons b w ih => simp [DynkinProjection.word_cons, ih]

theorem lift_freeEvaluate (U V : A) (p : WordCoefficients.Polynomial) :
    FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V) (freeEvaluate p) =
      evaluate U V p := by
  induction p with
  | nil => simp [freeEvaluate, evaluate]
  | cons t p ih =>
      change FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V)
        (t.1 • evaluateWord (FreeAlgebra.ι ℝ true) (FreeAlgebra.ι ℝ false) t.2 +
          freeEvaluate p) = _
      rw [map_add, map_smul, evaluateWord_free, lift_word, ih]
      rfl

theorem evaluate_logarithm_one (U V : A) : evaluate U V (logarithm 1) = U + V := by
  let : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℝ)
  rw [← BCHLogarithm.coeff_logOf_splitSeries, NoncommutativeSeries.coeff_logOf]
  simp [Finset.sum_range_succ, PowerSeries.coeff_one,
    BCHLogarithm.evaluate_exponential, add_comm]

end Evaluation

section Operators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

local instance : Algebra ℚ (Module.End ℝ E) :=
  Algebra.compHom (Module.End ℝ E) (algebraMap ℚ ℝ)

theorem lift_nested (U V : Module.End ℝ E) (w : Word) :
    FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V)
      (DynkinProjection.nested (R := ℝ) w) =
        (BCHCoefficients.wordExpression w).operator U V := by
  induction w with
  | nil => simp [BCHCoefficients.wordExpression, LieExpression.operator]
  | cons b w ih =>
      cases w with
      | nil => cases b <;> simp [BCHCoefficients.wordExpression, LieExpression.operator]
      | cons c w =>
          simp only [DynkinProjection.nested, map_sub, map_mul,
            FreeAlgebra.lift_ι_apply, BCHCoefficients.wordExpression,
            LieExpression.operator]
          rw [ih]
          cases b <;> rfl

theorem lift_dynkin_freeEvaluate (U V : Module.End ℝ E)
    (p : WordCoefficients.Polynomial) :
    FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V)
      (DynkinProjection.dynkin (freeEvaluate p)) =
        (BCHCoefficients.polynomialExpression p).operator U V := by
  induction p with
  | nil => simp [freeEvaluate, evaluate, BCHCoefficients.polynomialExpression,
      LieExpression.operator]
  | cons t p ih =>
      change FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V)
        (DynkinProjection.dynkin
          (t.1 • evaluateWord (FreeAlgebra.ι ℝ true) (FreeAlgebra.ι ℝ false) t.2 +
            freeEvaluate p)) = _
      rw [map_add, map_smul, map_add, map_smul, evaluateWord_free,
        DynkinProjection.dynkin_word, lift_nested, ih]
      rfl

/-- The canonical Lie expression represents the formal logarithm coefficient,
provided the universal coefficient is a Lie polynomial. -/
theorem coefficient_operator_of_isLie
    (hLie : ∀ n, DynkinProjection.IsLie (NoncommutativeSeries.universalCoefficient n))
    (U V : Module.End ℝ E) (r : ℕ) :
    (BCHCoefficients.coefficient (r + 1)).operator U V =
      PowerSeries.coeff (r + 1)
        (NoncommutativeSeries.logOf (BCHLogarithm.splitSeries U V)) := by
  rw [BCHLogarithm.coeff_logOf_splitSeries]
  cases r with
  | zero => simp [BCHCoefficients.coefficient, LieExpression.operator,
      evaluate_logarithm_one]
  | succ r =>
      have hproj := DynkinProjection.inv_degree_smul_dynkin_of_isLie
        (K := ℝ) (n := (r + 1) + 1)
        (by positivity : (((r + 1) + 1 : ℕ) : ℝ) ≠ 0)
        (freeEvaluate_logarithm_isLie _ (hLie _))
        (freeEvaluate_homogeneous _ _ (logarithm_homogeneous _))
      have h := congrArg (FreeAlgebra.lift ℝ (fun b : Bool => if b then U else V)) hproj
      rw [map_smul, lift_freeEvaluate] at h
      change (BCHCoefficients.polynomialExpression (correctionRepresentation (r + 1))).operator
        U V = _
      rw [← lift_dynkin_freeEvaluate]
      simpa only [correctionRepresentation, freeEvaluate, evaluate_scale, map_smul,
        one_div] using h

/-- Conditional adapter to the exact BCH interface used by the regret proof.
The only premise is explicit universal Lie membership; exponential inversion,
word coefficients, homogeneity, DSW, and the operator action are proved. -/
theorem classicalBCHInput_of_isLie
    (hLie : ∀ n, DynkinProjection.IsLie (NoncommutativeSeries.universalCoefficient n)) :
    ClassicalBCHInput BCHCoefficients.coefficient E where
  linear_coefficient := rfl
  exponentiate U V P := by
    let L := NoncommutativeSeries.logOf (BCHLogarithm.splitSeries U V)
    have hL : L.constantCoeff = 0 := NoncommutativeSeries.constantCoeff_logOf _
    have hgen : SeriesAction.act L = bchGenerator BCHCoefficients.coefficient U V := by
      funext Q
      rw [SeriesAction.act_eq_shift_applySeries hL]
      have hc : (fun n => PowerSeries.coeff (n + 1) L) =
          (fun n => (BCHCoefficients.coefficient (n + 1)).operator U V) := by
        funext n
        exact (coefficient_operator_of_isLie hLie U V n).symm
      rw [hc]
      rfl
    calc
      applySeries (splitFlowCoefficient U V) P =
          SeriesAction.act (BCHLogarithm.splitSeries U V) P := by
        rw [SeriesAction.act_eq_applySeries]
        congr 1
        funext n
        exact (BCHLogarithm.coeff_splitSeries_end U V n).symm
      _ = SeriesAction.act (NoncommutativeSeries.expOf L) P := by
        simp only [L, NoncommutativeSeries.expOf_logOf
          (BCHLogarithm.constantCoeff_splitSeries U V)]
      _ = expApply (SeriesAction.act L) P := SeriesAction.act_eval_exp hL P
      _ = expApply (bchGenerator BCHCoefficients.coefficient U V) P := by rw [hgen]

/-- The canonical BCH coefficients exponentiate to the ordered product of
exponentials. All universal Lie membership and formal-series identities used
by this theorem are proved in Lean. -/
theorem classicalBCHInput : ClassicalBCHInput BCHCoefficients.coefficient E :=
  classicalBCHInput_of_isLie BCH.Phi_isLie

end Operators

end

end AltOMD.BCHTheorem
