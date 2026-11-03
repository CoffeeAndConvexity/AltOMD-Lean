import AltOMD.Hamiltonian.HamiltonianSystem
import AltOMD.Hamiltonian.CoupledTensor
import AltOMD.Hamiltonian.BracketBounds

/-! The split Hamiltonian system of an actual bilinear game. -/

noncomputable section
open scoped ContDiff

namespace AltOMD.BilinearSystem

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def firstHamiltonian (f : E → ℝ) (hf : ContDiff ℝ ∞ f) : SmoothScalar (E × F) :=
  ⟨fun z => f z.1, hf.comp contDiff_fst⟩

def secondHamiltonian (g : F → ℝ) (hg : ContDiff ℝ ∞ g) : SmoothScalar (E × F) :=
  ⟨fun z => g z.2, hg.comp contDiff_snd⟩

def system (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : SplitHamiltonianSystem (E × F) where
  J := CoupledTensor.tensor A
  skew := CoupledTensor.tensor_skew A
  F := firstHamiltonian f hf
  G := secondHamiltonian g hg
  φF := Flow.shearF (fun u => A (gradient f u))
  φG := Flow.shearG (fun w => -A.adjoint (gradient g w))
  smoothF := Flow.contDiff_shearF _
  smoothG := Flow.contDiff_shearG _
  odeF := by
    intro z t
    change HasDerivAt (fun s => Flow.shearF (fun u => A (gradient f u)) s z)
      (CoupledTensor.tensor A (fderiv ℝ (fun p : E × F => f p.1)
        (Flow.shearF (fun u => A (gradient f u)) t z))) t
    rw [CoupledTensor.tensor_fderiv_first A _ (hf.differentiable (by simp) _)]
    exact Flow.hasDerivAt_shearF _ z t
  odeG := by
    intro z t
    change HasDerivAt (fun s => Flow.shearG (fun w => -A.adjoint (gradient g w)) s z)
      (CoupledTensor.tensor A (fderiv ℝ (fun p : E × F => g p.2)
        (Flow.shearG (fun w => -A.adjoint (gradient g w)) t z))) t
    rw [CoupledTensor.tensor_fderiv_second A _ (hg.differentiable (by simp) _)]
    exact Flow.hasDerivAt_shearG _ z t
  zeroF := Flow.shearF_zero _
  zeroG := Flow.shearG_zero _

@[simp] theorem system_energy (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : E × F) :
    (system A f g hf hg).energy z = f z.1 + g z.2 := rfl

/-- The actual alternating mirror update in dual coordinates. -/
theorem system_step (A : E →L[ℝ] F) (f : E → ℝ) (g : F → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (η : ℝ) (z : E × F) :
    (system A f g hf hg).step η z =
      (z.1 - η • A.adjoint (gradient g z.2),
        z.2 + η • A (gradient f (z.1 - η • A.adjoint (gradient g z.2)))) := by
  simp [SplitHamiltonianSystem.step, system, Flow.shearF, Flow.shearG,
    smul_neg, sub_eq_add_neg]

theorem bracketConstant_le (A : E →L[ℝ] F) (K : ℝ) :
    bracketConstant (CoupledTensor.tensor A) K ≤ 24 * max ‖A‖ 1 * K ^ 2 := by
  unfold bracketConstant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (max_le_max (CoupledTensor.tensor_norm_le A) le_rfl)
      (by norm_num)) (sq_nonneg K)

theorem first_regularity (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (K : ℝ)
    (hbound : ∀ r x, 1 ≤ r → ‖iteratedFDeriv ℝ r f x‖ ≤ K ^ r * r.factorial)
    (r : ℕ) (z : E × F) (hr : 1 ≤ r) :
    ‖iteratedFDeriv ℝ r (firstHamiltonian (F := F) f hf : E × F → ℝ) z‖ ≤ K ^ r * r.factorial :=
  (CoupledTensor.norm_iteratedFDeriv_first_le hf r z).trans (hbound r z.1 hr)

theorem second_regularity (g : F → ℝ) (hg : ContDiff ℝ ∞ g) (K : ℝ)
    (hbound : ∀ r x, 1 ≤ r → ‖iteratedFDeriv ℝ r g x‖ ≤ K ^ r * r.factorial)
    (r : ℕ) (z : E × F) (hr : 1 ≤ r) :
    ‖iteratedFDeriv ℝ r (secondHamiltonian (E := E) g hg : E × F → ℝ) z‖ ≤ K ^ r * r.factorial :=
  (CoupledTensor.norm_iteratedFDeriv_second_le hg r z).trans (hbound r z.2 hr)

end AltOMD.BilinearSystem
end
