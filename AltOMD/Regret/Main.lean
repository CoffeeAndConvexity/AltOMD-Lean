import AltOMD.Hamiltonian.HamiltonianSystem
import AltOMD.Hamiltonian.HamiltonianBounds
import AltOMD.Hamiltonian.EnergyDefect
import AltOMD.Regret.Regret

/-!
# Logarithmic regret from analytic Hamiltonian data

The modified-energy bounds in this theorem are conclusions of the coefficient,
derivative, formal cancellation, and real Taylor estimates. The only external
mathematical inputs are the named universal BCH and DSW identities.
-/

open scoped ContDiff
open Finset

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def hamiltonianCorrections (S : SplitHamiltonianSystem E)
    (Z : ℕ → FormalEnergy.LieExpression) (r : ℕ) : SmoothScalar E :=
  FormalEnergy.correctedHamiltonian (smoothPoissonBracket S.J) S.G S.F Z r

/-- Both estimates needed by the regret argument, proved from the derivative
assumptions and the two named algebraic inputs. -/
theorem hamiltonian_modified_energy_estimates (S : SplitHamiltonianSystem E)
    {K C η : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hCJ : bracketConstant S.J K ≤ C)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.F‖ ≤ K ^ r * r.factorial)
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar E))
    (dsw : WordCoefficients.ClassicalDSWInput Z (SmoothScalar E))
    (N : ℕ) (hη : 0 ≤ η) (hsmall : 16 * C * η * (N + 2) ≤ 1) (z : E) :
    |truncatedEnergy (fun r => (hamiltonianCorrections S Z r : E → ℝ)) N η z - S.energy z| ≤
        (64 / 3 : ℝ) * C ^ 2 * η ∧
      |truncatedEnergy (fun r => (hamiltonianCorrections S Z r : E → ℝ)) N η (S.step η z) -
        truncatedEnergy (fun r => (hamiltonianCorrections S Z r : E → ℝ)) N η z| ≤
          16 * Real.exp 2 * C ^ 2 * η / (4 : ℝ) ^ (N + 1) := by
  have hJ0 : 0 ≤ bracketConstant S.J K := by unfold bracketConstant; positivity
  have hmixed (r α β : ℕ) (hp : 0 < r + α + β) (x : E) :
      |Flow.lieIterate (hamiltonianField S.J S.G)
        (Flow.lieIterate (hamiltonianField S.J S.F)
          (hamiltonianCorrections S Z r : E → ℝ) β) α x| ≤
        (4 * C) ^ (r + α + β + 1) * ((r + α + β).factorial : ℝ) := by
    rw [mixed_lieIterate_hamiltonianField]
    have hb := norm_mixed_correction_le S.J S.skew S.G S.F hK hG hF Z dsw r α β x hp
    apply (show |((poissonGenerator S.J S.G ^ α * poissonGenerator S.J S.F ^ β)
      (hamiltonianCorrections S Z r) : E → ℝ) x| ≤
        (4 * bracketConstant S.J K) ^ (r + α + β + 1) *
          ((r + α + β).factorial : ℝ) from hb).trans
    gcongr
  have hzero : (hamiltonianCorrections S Z 0 : E → ℝ) = S.energy := by
    funext x
    have hz := smooth_correction_zero S.J S.G S.F Z bch
    exact congrArg (fun f : SmoothScalar E => (f : E → ℝ) x) hz
  have hclose := truncatedEnergy_close (fun r => (hamiltonianCorrections S Z r : E → ℝ))
    N hC hη hsmall (fun r hr x => by
      simpa [Flow.lieIterate] using hmixed (r + 1) 0 0 (by omega) x) z
  rw [hzero] at hclose
  refine ⟨hclose, ?_⟩
  have hdefect := EnergyDefect.factorial_defect_from_mixed_lie
    (fun r => (hamiltonianCorrections S Z r : E → ℝ))
    (contDiff_hamiltonianField S.J S.F) (contDiff_hamiltonianField S.J S.G)
    S.φF S.φG S.smoothF S.smoothG S.odeF S.odeG S.zeroF S.zeroG N
    (fun r _ => (hamiltonianCorrections S Z r).contDiff) hη hC z
    (fun j _ => EnergyDefect.corrected_scalar_cancellation S.J S.skew S.G S.F Z bch (j + 1) z)
    (fun r _ α β hp x => hmixed r α β hp x)
  exact hdefect.trans (factorial_defect_bound N hC hη hsmall)

lemma stepSize_small {C : ℝ} (hC : 0 < C) (T : ℕ) :
    16 * C * stepSize C T * ((Nat.log 2 T : ℝ) + 2) ≤ 1 := by
  have hd : 16 * C * ((Nat.log 2 T : ℝ) + 2) ≠ 0 := by positivity
  have heq := div_mul_cancel₀ (1 : ℝ) hd
  unfold stepSize
  nlinarith [heq]

/-- The full energy-to-regret theorem. Unlike `scheduled_regret_bound`, this
statement does not assume any modified-energy estimate. -/
theorem logarithmic_regret_two_bounds {Cmp : Type*} [Nonempty Cmp]
    (S : SplitHamiltonianSystem E) {K C Λ : ℝ}
    (hK : 1 ≤ K) (hC : 0 < C) (hΛ : 0 ≤ Λ)
    (hCJ : bracketConstant S.J K ≤ C)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.F‖ ≤ K ^ r * r.factorial)
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar E))
    (dsw : WordCoefficients.ClassicalDSWInput Z (SmoothScalar E))
    (T : ℕ) (z : ℕ → E) (cost : Cmp → ℕ → ℝ) (coupling : Cmp → ℕ → ℝ)
    (htrajectory : ∀ k < T, z (k + 1) = S.step (stepSize C T) (z k))
    (hcomparator : ∀ c k, k < T → stepSize C T * cost c k =
      S.energy (z (k + 1)) - S.energy (z k) + coupling c k - coupling c (k + 1))
    (hterminal : ∀ c, 0 ≤ coupling c T) (hinitial : ∀ c, coupling c 0 ≤ Λ) :
    totalRegret cost T ≤ 16 * C * Λ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C ^ 2 ∧
      16 * C * Λ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C ^ 2 ≤ 16 * C * Λ * (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C ^ 2 := by
  let M : ℕ → ℝ := fun k =>
    truncatedEnergy (fun r => (hamiltonianCorrections S Z r : E → ℝ)) (Nat.log 2 T) (stepSize C T) (z k)
  have hb (x : E) := hamiltonian_modified_energy_estimates S hK hC.le hCJ hG hF Z bch dsw
    (Nat.log 2 T) (stepSize_pos hC T).le (stepSize_small hC T) x
  apply scheduled_regret_bound_two_bounds cost (fun k => S.energy (z k)) M coupling T C Λ hC hΛ
    hcomparator hterminal hinitial
  · simpa only [M, abs_sub_comm] using (hb (z 0)).1
  · simpa only [M, abs_sub_comm] using (hb (z T)).1
  · intro k hk
    dsimp [M]
    rw [htrajectory k hk]
    exact (hb (z k)).2

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem logarithmic_regret {Cmp : Type*} [Nonempty Cmp]
    (S : SplitHamiltonianSystem E) {K C Λ : ℝ}
    (hK : 1 ≤ K) (hC : 0 < C) (hΛ : 0 ≤ Λ)
    (hCJ : bracketConstant S.J K ≤ C)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x S.F‖ ≤ K ^ r * r.factorial)
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar E))
    (dsw : WordCoefficients.ClassicalDSWInput Z (SmoothScalar E))
    (T : ℕ) (z : ℕ → E) (cost : Cmp → ℕ → ℝ) (coupling : Cmp → ℕ → ℝ)
    (htrajectory : ∀ k < T, z (k + 1) = S.step (stepSize C T) (z k))
    (hcomparator : ∀ c k, k < T → stepSize C T * cost c k =
      S.energy (z (k + 1)) - S.energy (z k) + coupling c k - coupling c (k + 1))
    (hterminal : ∀ c, 0 ≤ coupling c T) (hinitial : ∀ c, coupling c 0 ≤ Λ) :
    totalRegret cost T ≤ 16 * C * Λ * (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C ^ 2 := by
  have h := logarithmic_regret_two_bounds S hK hC hΛ hCJ hG hF Z bch dsw T z cost coupling htrajectory hcomparator hterminal hinitial
  exact h.1.trans h.2

end AltOMD
