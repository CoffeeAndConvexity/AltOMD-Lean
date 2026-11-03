import AltOMD.Regret.Main
import AltOMD.Hamiltonian.BilinearSystem
import AltOMD.Hamiltonian.BCHTheorem

/-! Finite modified-energy bounds with the canonical BCH coefficients. -/

open scoped ContDiff InnerProductSpace

namespace AltOMD

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quantitative energy theorem with its algebraic inputs supplied by the
proved canonical BCH construction. -/
theorem canonical_hamiltonian_modified_energy_estimates (S : SplitHamiltonianSystem E)
    {K C η : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hCJ : bracketConstant S.J K ≤ C)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.F‖ ≤ K ^ r * r.factorial)
    (N : ℕ) (hη : 0 ≤ η) (hsmall : 16 * C * η * (N + 2) ≤ 1) (z : E) :
    |truncatedEnergy (fun r =>
        (hamiltonianCorrections S BCHCoefficients.coefficient r : E → ℝ)) N η z -
        S.energy z| ≤ (64 / 3 : ℝ) * C ^ 2 * η ∧
      |truncatedEnergy (fun r =>
          (hamiltonianCorrections S BCHCoefficients.coefficient r : E → ℝ))
          N η (S.step η z) -
        truncatedEnergy (fun r =>
          (hamiltonianCorrections S BCHCoefficients.coefficient r : E → ℝ)) N η z| ≤
        16 * Real.exp 2 * C ^ 2 * η / (4 : ℝ) ^ (N + 1) := by
  exact hamiltonian_modified_energy_estimates S hK hC hCJ hG hF
    BCHCoefficients.coefficient BCHTheorem.classicalBCHInput
    BCHCoefficients.classicalDSWInput N hη hsmall z

end General

section Bilinear

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Sharpened finite modified-energy estimates for the actual alternating
bilinear update. The summed derivative assumption supplies the separate bounds;
the canonical coefficients and both algebraic identities are internal. -/
theorem canonical_bilinear_modified_energy_estimates
    (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {K η : ℝ} (hK : 1 ≤ K)
    (hderivative : ∀ r, 1 ≤ r → ∀ u w,
      ‖iteratedFDeriv ℝ r f u‖ + ‖iteratedFDeriv ℝ r g w‖ ≤ K ^ r * r.factorial)
    (N : ℕ) (hη : 0 < η)
    (hsmall : η ≤ 1 / (16 * (24 * max ‖A‖ 1 * K ^ 2) * (N + 2)))
    (z : E × F) :
    let S := BilinearSystem.system A f g hf hg
    let H := fun r => (hamiltonianCorrections S BCHCoefficients.coefficient r : E × F → ℝ)
    let C₀ := 24 * max ‖A‖ 1 * K ^ 2
    |truncatedEnergy H N η z - (f z.1 + g z.2)| ≤ (64 / 3 : ℝ) * C₀ ^ 2 * η ∧
      |truncatedEnergy H N η
          (z.1 - η • A.adjoint (gradient g z.2),
            z.2 + η • A (gradient f (z.1 - η • A.adjoint (gradient g z.2)))) -
        truncatedEnergy H N η z| ≤
          16 * Real.exp 2 * C₀ ^ 2 * η / (4 : ℝ) ^ (N + 1) := by
  let S := BilinearSystem.system A f g hf hg
  let C₀ := 24 * max ‖A‖ 1 * K ^ 2
  have hC : 0 < C₀ := by
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    dsimp only [C₀]
    positivity
  have hsmall' : 16 * C₀ * η * (N + 2) ≤ 1 := by
    have hden : 0 < 16 * C₀ * (N + 2) := by positivity
    have h := (le_div_iff₀ hden).mp hsmall
    nlinarith
  have hF : ∀ r u, 1 ≤ r → ‖iteratedFDeriv ℝ r f u‖ ≤ K ^ r * r.factorial := by
    intro r u hr
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hderivative r hr u 0)
  have hG : ∀ r w, 1 ≤ r → ‖iteratedFDeriv ℝ r g w‖ ≤ K ^ r * r.factorial := by
    intro r w hr
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hderivative r hr 0 w)
  have hb := canonical_hamiltonian_modified_energy_estimates S hK hC.le
    (BilinearSystem.bracketConstant_le A K)
    (BilinearSystem.second_regularity g hg K hG)
    (BilinearSystem.first_regularity f hf K hF) N hη.le hsmall' z
  have henergy : S.energy z = f z.1 + g z.2 := rfl
  have hstep : S.step η z =
      (z.1 - η • A.adjoint (gradient g z.2),
        z.2 + η • A (gradient f (z.1 - η • A.adjoint (gradient g z.2)))) :=
    BilinearSystem.system_step A f g hf hg η z
  dsimp only
  rw [← henergy, ← hstep]
  exact hb

end Bilinear

end AltOMD
