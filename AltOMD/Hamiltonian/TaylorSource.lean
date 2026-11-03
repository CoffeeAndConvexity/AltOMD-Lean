import AltOMD.Hamiltonian.BilinearSystem

/-! The manuscript's global Taylor bound for the actual Hamiltonian shears. -/

noncomputable section
open scoped ContDiff BigOperators
open Finset

namespace AltOMD

namespace SplitHamiltonianSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A global mixed Lie-derivative bound implies the Taylor remainder bound.
The flow equations are supplied by the Hamiltonian system. -/
theorem taylor_remainder (S : SplitHamiltonianSystem E) (f : SmoothScalar E)
    (m : ℕ) (z : E) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ α β : ℕ, α + β = m + 1 → ∀ p : E,
      |((poissonGenerator S.J S.G ^ α * poissonGenerator S.J S.F ^ β) f : E → ℝ) p| ≤ M) :
    |(f : E → ℝ) (S.step h z) -
      ∑ β ∈ range (m + 1), ∑ α ∈ range (m - β + 1),
        h ^ (α + β) / ((α.factorial : ℝ) * β.factorial) *
          ((poissonGenerator S.J S.G ^ α * poissonGenerator S.J S.F ^ β) f : E → ℝ) z| ≤
      (2 : ℝ) ^ (m + 1) * M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hMF : ∀ t ∈ Set.Icc 0 h,
      |Flow.lieIterate (hamiltonianField S.J S.F) (f : E → ℝ) (m + 1)
        (S.φF t (S.φG h z))| ≤ M := by
    intro t ht
    simpa only [zero_add, pow_zero, one_mul, lieIterate_hamiltonianField] using
      hM 0 (m + 1) (by omega) (S.φF t (S.φG h z))
  have hMG : ∀ β ≤ m, ∀ t ∈ Set.Icc 0 h,
      |Flow.lieIterate (hamiltonianField S.J S.G)
        (Flow.lieIterate (hamiltonianField S.J S.F) (f : E → ℝ) β)
        (m - β + 1) (S.φG t z)| ≤ M := by
    intro β hβ t ht
    rw [mixed_lieIterate_hamiltonianField]
    exact hM _ _ (by omega) _
  have hb := Flow.two_flow_remainder
    (contDiff_hamiltonianField S.J S.F) (contDiff_hamiltonianField S.J S.G)
    f.contDiff S.φF S.φG S.smoothF S.smoothG S.odeF S.odeG S.zeroF S.zeroG
    m z hh hMF hMG
  have hp : Flow.triangularTaylor (hamiltonianField S.J S.F)
      (hamiltonianField S.J S.G) (f : E → ℝ) m h z =
      ∑ β ∈ range (m + 1), ∑ α ∈ range (m - β + 1),
        h ^ (α + β) / ((α.factorial : ℝ) * β.factorial) *
          ((poissonGenerator S.J S.G ^ α * poissonGenerator S.J S.F ^ β) f : E → ℝ) z := by
    unfold Flow.triangularTaylor
    apply sum_congr rfl
    intro β hβ
    rw [mul_sum]
    apply sum_congr rfl
    intro α hα
    rw [mixed_lieIterate_hamiltonianField, pow_add]
    ring
  simpa only [hp, SplitHamiltonianSystem.step] using hb

end SplitHamiltonianSystem

namespace BilinearSystem

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Lemma `lem:real-taylor-composition`, with the AltOMD shear written explicitly.
The mixed derivatives are globally bounded, as in the manuscript. -/
theorem taylor_remainder_source (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (H : SmoothScalar (E × F))
    (m : ℕ) (z : E × F) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ α β : ℕ, α + β = m + 1 → ∀ p : E × F,
      |((poissonGenerator (CoupledTensor.tensor A) (secondHamiltonian g hg) ^ α *
        poissonGenerator (CoupledTensor.tensor A) (firstHamiltonian f hf) ^ β) H :
          E × F → ℝ) p| ≤ M) :
    |(H : E × F → ℝ) (z.1 - h • A.adjoint (gradient g z.2),
        z.2 + h • A (gradient f (z.1 - h • A.adjoint (gradient g z.2)))) -
      ∑ β ∈ range (m + 1), ∑ α ∈ range (m - β + 1),
        h ^ (α + β) / ((α.factorial : ℝ) * β.factorial) *
          ((poissonGenerator (CoupledTensor.tensor A) (secondHamiltonian g hg) ^ α *
            poissonGenerator (CoupledTensor.tensor A) (firstHamiltonian f hf) ^ β) H :
              E × F → ℝ) z| ≤
      (2 : ℝ) ^ (m + 1) * M * h ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  have hb := (system A f g hf hg).taylor_remainder H m z hh hM
  rw [system_step] at hb
  exact hb

end BilinearSystem
end AltOMD
