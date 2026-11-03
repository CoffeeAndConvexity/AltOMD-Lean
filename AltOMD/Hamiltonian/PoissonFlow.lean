import AltOMD.Hamiltonian.Poisson
import AltOMD.Hamiltonian.Flow

/-! Identification of the algebraic Hamiltonian generators with actual
directional derivatives along the Hamiltonian vector fields. -/

noncomputable section
open scoped ContDiff

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hamiltonianField (J : (E →L[ℝ] ℝ) →L[ℝ] E) (Q : SmoothScalar E) (z : E) : E :=
  J (fderiv ℝ (Q : E → ℝ) z)

theorem contDiff_hamiltonianField (J : (E →L[ℝ] ℝ) →L[ℝ] E) (Q : SmoothScalar E) :
    ContDiff ℝ ∞ (hamiltonianField J Q) :=
  J.contDiff.comp (Q.contDiff.fderiv_right (by simp))

theorem lieIterate_hamiltonianField (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (Q f : SmoothScalar E) (k : ℕ) :
    Flow.lieIterate (hamiltonianField J Q) (f : E → ℝ) k =
      ((poissonGenerator J Q ^ k) f : E → ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Flow.lieIterate, ih, pow_succ']
    rfl

theorem mixed_lieIterate_hamiltonianField (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G F f : SmoothScalar E) (α β : ℕ) :
    Flow.lieIterate (hamiltonianField J G)
      (Flow.lieIterate (hamiltonianField J F) (f : E → ℝ) β) α =
      ((poissonGenerator J G ^ α * poissonGenerator J F ^ β) f : E → ℝ) := by
  rw [lieIterate_hamiltonianField, lieIterate_hamiltonianField]
  rfl

end AltOMD
