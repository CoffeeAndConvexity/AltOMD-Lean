import AltOMD.Entropy.Shannon
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The extended-real Shannon regularizer

`extendedEntropy` is the literal function in the manuscript: negative Shannon
entropy on the closed simplex and `+∞` outside. The real-valued `entropy`
represents its finite values and supplies ambient derivatives at positive
vectors. `Duality.conjugate simplex entropy` restricts its supremum to exactly
the effective domain identified here.
-/

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι]

open Set Filter
open scoped Topology

/-- Negative Shannon entropy with effective domain equal to the closed simplex. -/
noncomputable def extendedEntropy (x : EuclideanSpace ℝ ι) : EReal := by
  classical
  exact if x ∈ simplex then (entropy x : EReal) else ⊤

theorem extendedEntropy_of_mem {x : EuclideanSpace ℝ ι} (hx : x ∈ simplex) :
    extendedEntropy x = (entropy x : EReal) := by
  simp [extendedEntropy, hx]

theorem extendedEntropy_of_not_mem {x : EuclideanSpace ℝ ι} (hx : x ∉ simplex) :
    extendedEntropy x = ⊤ := by
  simp [extendedEntropy, hx]

@[simp] theorem extendedEntropy_ne_bot (x : EuclideanSpace ℝ ι) :
    extendedEntropy x ≠ ⊥ := by
  classical
  by_cases hx : x ∈ simplex <;> simp [extendedEntropy, hx]

@[simp] theorem extendedEntropy_lt_top_iff (x : EuclideanSpace ℝ ι) :
    extendedEntropy x < ⊤ ↔ x ∈ simplex := by
  classical
  by_cases hx : x ∈ simplex <;> simp [extendedEntropy, hx]

/-- Boundary points of the closed simplex remain in the effective domain. -/
theorem effectiveDomain_extendedEntropy :
    {x : EuclideanSpace ℝ ι | extendedEntropy x < ⊤} = simplex := by
  ext x
  exact extendedEntropy_lt_top_iff x

theorem entropy_coe_le_extendedEntropy (x : EuclideanSpace ℝ ι) :
    (entropy x : EReal) ≤ extendedEntropy x := by
  classical
  by_cases hx : x ∈ simplex <;> simp [extendedEntropy, hx]

/-- The extended-real regularizer is lower semicontinuous on the entire space. -/
theorem lowerSemicontinuous_extendedEntropy :
    LowerSemicontinuous (extendedEntropy : EuclideanSpace ℝ ι → EReal) := by
  intro x b hb
  by_cases hx : x ∈ simplex
  · have hb' : b < (entropy x : EReal) := by
      simpa [extendedEntropy, hx] using hb
    have hc := (continuous_coe_real_ereal.comp continuous_entropy).lowerSemicontinuous x b hb'
    filter_upwards [hc] with y hy
    exact hy.trans_le (entropy_coe_le_extendedEntropy y)
  · have hout : ∀ᶠ y in 𝓝 x, y ∉ (simplex : Set (EuclideanSpace ℝ ι)) :=
      isCompact_simplex.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [hout] with y hy
    simpa [extendedEntropy, hx, hy] using hb

/-- Properness: the regularizer never takes `−∞` and has a finite value. -/
theorem extendedEntropy_proper [Nonempty ι] :
    (∀ x : EuclideanSpace ℝ ι, extendedEntropy x ≠ ⊥) ∧
      ∃ x : EuclideanSpace ℝ ι, extendedEntropy x < ⊤ :=
  ⟨extendedEntropy_ne_bot, uniform,
    (extendedEntropy_lt_top_iff uniform).mpr uniform_mem_simplex⟩

theorem extendedEntropy_epigraph :
    {p : EuclideanSpace ℝ ι × ℝ | extendedEntropy p.1 ≤ (p.2 : EReal)} =
      {p | p.1 ∈ simplex ∧ entropy p.1 ≤ p.2} := by
  classical
  ext p
  change extendedEntropy p.1 ≤ (p.2 : EReal) ↔ p.1 ∈ simplex ∧ entropy p.1 ≤ p.2
  by_cases hp : p.1 ∈ simplex
  · rw [extendedEntropy_of_mem hp]
    simp only [hp, true_and, EReal.coe_le_coe_iff]
  · rw [extendedEntropy_of_not_mem hp]
    simp only [hp, false_and]
    simp

/-- Convexity of the extended-real regularizer through its real epigraph. -/
theorem convex_epigraph_extendedEntropy :
    Convex ℝ {p : EuclideanSpace ℝ ι × ℝ | extendedEntropy p.1 ≤ (p.2 : EReal)} := by
  rw [extendedEntropy_epigraph]
  exact convexOn_entropy.convex_epigraph

theorem isClosed_epigraph_extendedEntropy :
    IsClosed {p : EuclideanSpace ℝ ι × ℝ | extendedEntropy p.1 ≤ (p.2 : EReal)} := by
  rw [extendedEntropy_epigraph]
  exact (lowerSemicontinuousOn_iff_isClosed_epigraph isCompact_simplex.isClosed).mp
    (continuous_entropy.lowerSemicontinuous.lowerSemicontinuousOn simplex)

/-- The literal extended-real Fenchel supremum is finite and equals log-sum-exp. -/
theorem extendedEntropy_fenchel_eq_logSumExp [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    (⨆ x : EuclideanSpace ℝ ι, ((inner ℝ u x : ℝ) : EReal) - extendedEntropy x) =
      (logSumExp u : EReal) := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    by_cases hx : x ∈ simplex
    · rw [extendedEntropy_of_mem hx, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact conjugate_objective_le u hx
    · simp [extendedEntropy_of_not_mem hx]
  · have h : ((inner ℝ u (softmax u) : ℝ) : EReal) -
        extendedEntropy (softmax u) = (logSumExp u : EReal) := by
      rw [extendedEntropy_of_mem (softmax_mem_simplex u), ← EReal.coe_sub,
        conjugate_objective_softmax u]
    rw [← h]
    exact le_iSup (fun x : EuclideanSpace ℝ ι =>
      ((inner ℝ u x : ℝ) : EReal) - extendedEntropy x) (softmax u)

end AltOMD.Shannon
