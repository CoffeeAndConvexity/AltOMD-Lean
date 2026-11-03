import AltOMD.Hamiltonian.PoissonFlow

/-! Data for two smooth Hamiltonians with their actual flows. -/

open scoped ContDiff

namespace AltOMD

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flow equations are geometric data. No formal preservation or
quantitative modified-energy estimate is included in this structure. -/
structure SplitHamiltonianSystem where
  J : (E →L[ℝ] ℝ) →L[ℝ] E
  skew : IsSkewPoissonTensor J
  F : SmoothScalar E
  G : SmoothScalar E
  φF : ℝ → E → E
  φG : ℝ → E → E
  smoothF : ∀ z, ContDiff ℝ ∞ (fun t => φF t z)
  smoothG : ∀ z, ContDiff ℝ ∞ (fun t => φG t z)
  odeF : ∀ z t, HasDerivAt (fun s => φF s z) (hamiltonianField J F (φF t z)) t
  odeG : ∀ z t, HasDerivAt (fun s => φG s z) (hamiltonianField J G (φG t z)) t
  zeroF : ∀ z, φF 0 z = z
  zeroG : ∀ z, φG 0 z = z

namespace SplitHamiltonianSystem

variable {E}

noncomputable def energy (S : SplitHamiltonianSystem E) (z : E) : ℝ := (S.F : E → ℝ) z + (S.G : E → ℝ) z

def step (S : SplitHamiltonianSystem E) (η : ℝ) (z : E) : E := S.φF η (S.φG η z)

end SplitHamiltonianSystem
end AltOMD
