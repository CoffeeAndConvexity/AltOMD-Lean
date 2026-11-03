import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Shannon entropy on a finite simplex

These definitions use the Euclidean norm and the manuscript's convention
`0 * log 0 = 0`. The effective domain is recorded separately as `simplex`.
-/

open scoped BigOperators

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι]

/-- The closed probability simplex in Euclidean space. -/
def simplex : Set (EuclideanSpace ℝ ι) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- Negative Shannon entropy, restricted to `simplex` when used as a regularizer. -/
noncomputable def entropy (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, x i * Real.log (x i)

/-- The logarithm of the finite exponential sum. -/
noncomputable def logSumExp (u : EuclideanSpace ℝ ι) : ℝ :=
  Real.log (∑ i, Real.exp (u i))

/-- The normalized exponential vector. -/
noncomputable def softmax (u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.exp (u i) / ∑ j, Real.exp (u j))

/-- An ambient gradient of entropy at a vector with positive coordinates. -/
noncomputable def entropyGradient (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => 1 + Real.log (x i))

/-- The uniform probability vector. -/
noncomputable def uniform : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (Fintype.card ι : ℝ)⁻¹)

@[simp] theorem mem_simplex {x : EuclideanSpace ℝ ι} :
    x ∈ simplex ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := Iff.rfl

@[simp] theorem softmax_apply (u : EuclideanSpace ℝ ι) (i : ι) :
    softmax u i = Real.exp (u i) / ∑ j, Real.exp (u j) := rfl

@[simp] theorem entropyGradient_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    entropyGradient x i = 1 + Real.log (x i) := rfl

@[simp] theorem uniform_apply (i : ι) :
    (uniform : EuclideanSpace ℝ ι) i = (Fintype.card ι : ℝ)⁻¹ := rfl

end AltOMD.Shannon
