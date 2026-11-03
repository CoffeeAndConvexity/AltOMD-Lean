import AltOMD.Entropy.Shannon.LogarithmicRegret

/-!
# Alternating multiplicative weights on its source domain

The state consists of strictly positive simplex points and the step size is
positive. The normalized updates therefore have positive denominators on the
entire declared carrier. The ambient implementation remains available through
`multiplicativeWeights` and `alternatingWeights`.
-/

open scoped BigOperators InnerProductSpace

namespace AltOMD.Shannon

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

/-- Strictly positive probability vectors, including both source conditions. -/
abbrev PositiveSimplex (ι : Type*) [Fintype ι] :=
  {x : EuclideanSpace ℝ ι // x ∈ simplex ∧ ∀ i, 0 < x i}

/-- The positive constant step sizes used by the algorithm. -/
abbrev PositiveStepSize := {η : ℝ // 0 < η}

/-- Uniform initialization as a strictly positive probability vector. -/
noncomputable def positiveUniform : PositiveSimplex ι :=
  ⟨uniform, uniform_mem_simplex, uniform_pos⟩

theorem positive_denominator (x : PositiveSimplex ι)
    (a : EuclideanSpace ℝ ι) (η : PositiveStepSize) :
    0 < ∑ j, x.val j * Real.exp (-(η : ℝ) * a j) := by
  exact Finset.sum_pos (fun j _ => mul_pos (x.property.2 j) (Real.exp_pos _))
    Finset.univ_nonempty

/-- The normalized multiplicative update on the strictly positive simplex. -/
noncomputable def simplexWeights (x : PositiveSimplex ι)
    (a : EuclideanSpace ℝ ι) (η : PositiveStepSize) : PositiveSimplex ι :=
  ⟨multiplicativeWeights x.val a η,
    multiplicativeWeights_mem_simplex x.property.2 a η,
    multiplicativeWeights_pos x.property.2 a η⟩

@[simp] theorem simplexWeights_apply (x : PositiveSimplex ι)
    (a : EuclideanSpace ℝ ι) (η : PositiveStepSize) (i : ι) :
    (simplexWeights x a η).val i =
      x.val i * Real.exp (-(η : ℝ) * a i) /
        ∑ j, x.val j * Real.exp (-(η : ℝ) * a j) := rfl

/-- The actual alternating update, with the second loss evaluated at the new
first-player strategy. Every iterate belongs to the source state space. -/
noncomputable def alternatingSimplex
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) :
    ℕ → PositiveSimplex ι × PositiveSimplex κ
  | 0 => (x₀, y₀)
  | k + 1 =>
      let z := alternatingSimplex A η x₀ y₀ k
      let x := simplexWeights z.1 (A.adjoint z.2.val) η
      (x, simplexWeights z.2 (-A x.val) η)

@[simp] theorem alternatingSimplex_zero
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) :
    alternatingSimplex A η x₀ y₀ 0 = (x₀, y₀) := rfl

theorem alternatingSimplex_step_left
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) :
    (alternatingSimplex A η x₀ y₀ (k + 1)).1.val =
      multiplicativeWeights (alternatingSimplex A η x₀ y₀ k).1.val
        (A.adjoint (alternatingSimplex A η x₀ y₀ k).2.val) η := rfl

theorem alternatingSimplex_step_right
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) :
    (alternatingSimplex A η x₀ y₀ (k + 1)).2.val =
      multiplicativeWeights (alternatingSimplex A η x₀ y₀ k).2.val
        (-A (alternatingSimplex A η x₀ y₀ (k + 1)).1.val) η := rfl

/-- The first source coordinate update, including its normalizing denominator. -/
theorem alternatingSimplex_coordinate_left
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) (i : ι) :
    let z := alternatingSimplex A η x₀ y₀
    (z (k + 1)).1.val i = (z k).1.val i *
      Real.exp (-(η : ℝ) * (A.adjoint (z k).2.val) i) /
      ∑ j, (z k).1.val j * Real.exp (-(η : ℝ) * (A.adjoint (z k).2.val) j) := rfl

/-- The second source coordinate update uses the new first-player iterate. -/
theorem alternatingSimplex_coordinate_right
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) (i : κ) :
    let z := alternatingSimplex A η x₀ y₀
    (z (k + 1)).2.val i = (z k).2.val i *
      Real.exp ((η : ℝ) * (A (z (k + 1)).1.val) i) /
      ∑ j, (z k).2.val j * Real.exp ((η : ℝ) * (A (z (k + 1)).1.val) j) := by
  dsimp only
  rw [alternatingSimplex_step_right]
  exact multiplicativeWeights_neg_apply _ _ _ _

theorem alternatingSimplex_feasible
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) :
    ((alternatingSimplex A η x₀ y₀ k).1.val ∈ simplex ∧
      ∀ i, 0 < (alternatingSimplex A η x₀ y₀ k).1.val i) ∧
    ((alternatingSimplex A η x₀ y₀ k).2.val ∈ simplex ∧
      ∀ j, 0 < (alternatingSimplex A η x₀ y₀ k).2.val j) :=
  ⟨(alternatingSimplex A η x₀ y₀ k).1.property,
    (alternatingSimplex A η x₀ y₀ k).2.property⟩

/-- The source-domain recursion is the existing ambient implementation at
these valid initial states and step size. -/
theorem alternatingSimplex_coe
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (η : PositiveStepSize) (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (k : ℕ) :
    ((alternatingSimplex A η x₀ y₀ k).1.val,
      (alternatingSimplex A η x₀ y₀ k).2.val) =
      alternatingWeights A η x₀.val y₀.val k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact congrArg (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ =>
        let x := multiplicativeWeights z.1 (A.adjoint z.2) (η : ℝ)
        (x, multiplicativeWeights z.2 (-A x) (η : ℝ))) ih

/-- The horizon-dependent constant step with the improved entropy constant. -/
noncomputable def entropyStepSize
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (T : ℕ) (_hT : 1 ≤ T) :
    PositiveStepSize :=
  ⟨stepSize (entropyGameConstant A) T,
    stepSize_pos (by unfold entropyGameConstant; positivity) T⟩

@[simp] theorem entropyStepSize_val
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (T : ℕ) (hT : 1 ≤ T) :
    (entropyStepSize A T hT : ℝ) =
      1 / (16 * entropyGameConstant A * (Nat.log 2 T + 2)) := rfl

/-- The entropy corollary for the recursion on its positive-simplex state
space. No analytic, geometric, or trajectory premise remains. -/
theorem alternatingSimplex_regret
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (x₀ : PositiveSimplex ι) (y₀ : PositiveSimplex κ) (T : ℕ) (hT : 1 ≤ T) :
    let z := alternatingSimplex A (entropyStepSize A T hT) x₀ y₀
    PrimalRegret.sumRegret simplex simplex A (fun k => (z k).1.val) (fun k => (z k).2.val) T ≤
      16 * entropyGameConstant A *
        (Real.log (1 / minCoordinate x₀.val) + Real.log (1 / minCoordinate y₀.val)) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  dsimp only
  apply logarithmic_regret A T hT _ _ x₀.property.1 y₀.property.1
    x₀.property.2 y₀.property.2
  · intro k _
    exact alternatingSimplex_step_left A _ x₀ y₀ k
  · intro k _
    exact alternatingSimplex_step_right A _ x₀ y₀ k

/-- The uniform-initialization bound for the same source-domain algorithm. -/
theorem alternatingSimplex_regret_uniform
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (T : ℕ) (hT : 1 ≤ T) :
    let z := alternatingSimplex A (entropyStepSize A T hT) positiveUniform positiveUniform
    PrimalRegret.sumRegret simplex simplex A (fun k => (z k).1.val) (fun k => (z k).2.val) T ≤
      16 * entropyGameConstant A * Real.log ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)) *
        (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * entropyGameConstant A ^ 2 := by
  dsimp only
  apply logarithmic_regret_uniform A T hT _ _ rfl rfl
  · intro k _
    exact alternatingSimplex_step_left A _ positiveUniform positiveUniform k
  · intro k _
    exact alternatingSimplex_step_right A _ positiveUniform positiveUniform k

end AltOMD.Shannon
