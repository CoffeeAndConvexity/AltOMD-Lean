import AltOMD.Entropy.Polarization
import AltOMD.Entropy.Banach
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The Euclidean-space polarization statement used in the entropy appendix. -/

namespace AltOMD.Polarization

/-- Banach's norm equality in `prop:power-series-polarization-input` on ℝᵈ. -/
theorem euclidean_norm_eq_diagonal_sup (d : ℕ) {s : ℕ} (hs : 1 ≤ s)
    (M : (EuclideanSpace ℝ (Fin d)) [×s]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin s)) (v : Fin s → EuclideanSpace ℝ (Fin d)),
      M (v ∘ σ) = M v) :
    ‖M‖ = sSup ((fun h : EuclideanSpace ℝ (Fin d) => |M (fun _ => h)|) ''
      Metric.closedBall 0 1) :=
  norm_eq_diagonal_sup hs M hM

/-- The earlier exponential polarization bound, retained for compatibility. -/
theorem euclidean_polarization (d : ℕ) {s : ℕ} (hs : 1 ≤ s)
    (M : (EuclideanSpace ℝ (Fin d)) [×s]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin s)) (v : Fin s → EuclideanSpace ℝ (Fin d)),
      M (v ∘ σ) = M v) :
    ‖M‖ ≤ Real.exp s *
      sSup ((fun h : EuclideanSpace ℝ (Fin d) => |M (fun _ => h)|) ''
        Metric.closedBall 0 1) :=
  real_polarization hs M hM

end AltOMD.Polarization
