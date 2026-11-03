import AltOMD.Entropy.LegendreMirror
import AltOMD.Regret.PrimalRegret

/-!
# Primal trajectories with automatic interior preservation

A primal run records only its interior initialization and feasible minimizers.
The Legendre boundary condition proves that every subsequent point is interior.
Compactness and differentiability of the conjugate also give a concrete,
globally defined alternating run satisfying these primal minimization updates.
-/

open Set
open scoped InnerProductSpace

namespace AltOMD.LegendreTrajectory

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The primal algorithm, without an interiority or differentiability assumption
on any iterate after initialization. -/
structure IsPrimalMirrorTrajectory (D : Set E) (ψ : E → ℝ) (η : ℝ)
    (loss x : ℕ → E) (T : ℕ) : Prop where
  initialri : x 0 ∈ intrinsicInterior ℝ D
  next_mem : ∀ k < T, x (k + 1) ∈ D
  minimizes : ∀ k < T, ∀ c ∈ D,
    η * ⟪loss k, x (k + 1)⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D (x k)) (x (k + 1)) (x k) ≤
      η * ⟪loss k, c⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D (x k)) c (x k)

/-- Optimality supplies a finite support, so Legendre steepness excludes every
boundary minimizer, including the terminal iterate. -/
theorem IsPrimalMirrorTrajectory.interior {D : Set E} {ψ : E → ℝ} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ}
    (hrun : IsPrimalMirrorTrajectory D ψ η loss x T)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ) :
    ∀ k ≤ T, x k ∈ intrinsicInterior ℝ D := by
  intro k hk
  cases k with
  | zero => exact hrun.initialri
  | succ k =>
      exact LegendreMirror.mirror_minimizer_mem_intrinsicInterior
        hψ hdiff hsteep hrun.initialri (hrun.next_mem k hk) (hrun.minimizes k hk)

/-- The interior and differentiability fields required by the primal-to-dual
regret proof are now derived from the regularizer assumptions. -/
theorem IsPrimalMirrorTrajectory.toIsMirrorTrajectory
    {D : Set E} {ψ : E → ℝ} {η : ℝ} {loss x : ℕ → E} {T : ℕ}
    (hrun : IsPrimalMirrorTrajectory D ψ η loss x T)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ) :
    PrimalRegret.IsMirrorTrajectory D ψ η loss x T := by
  exact ⟨fun k hk => hrun.interior hψ hdiff hsteep k (Nat.le_of_lt hk),
    fun k hk => hdiff _ (hrun.interior hψ hdiff hsteep k (Nat.le_of_lt hk)),
    hrun.next_mem, hrun.minimizes⟩

/-- A concrete choice of the unique primal mirror minimizer. -/
noncomputable def mirrorStep (D : Set E) (ψ : E → ℝ) (η : ℝ) (a x : E) : E :=
  gradient (Duality.conjugate D ψ) (gradientWithin ψ D x - η • a)

/-- This choice is interior and uniquely minimizes the actual primal objective.
In particular no hypothesis on the proposed next point is required. -/
theorem mirrorStep_spec {D : Set E} {ψ : E → ℝ} {η : ℝ} {p a x : E}
    (hcompact : IsCompact D) (hlsc : LowerSemicontinuousOn ψ D)
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hp : p ∈ intrinsicInterior ℝ D)
    (hdual : Differentiable ℝ (Duality.conjugate D ψ)) :
    mirrorStep D ψ η a x ∈ intrinsicInterior ℝ D ∧
      IsMinOn (fun z => η * ⟪a, z⟫_ℝ +
        Duality.bregman ψ (gradientWithin ψ D x) z x) D (mirrorStep D ψ η a x) ∧
      ∀ y ∈ D,
        IsMinOn (fun z => η * ⟪a, z⟫_ℝ +
          Duality.bregman ψ (gradientWithin ψ D x) z x) D y ↔
            y = mirrorStep D ψ η a x := by
  exact LegendreMirror.compact_mirror_step_interior
    hcompact hlsc hψ hdiff hsteep hp (hdual _)

/-- The alternating primal scheme, with the second player using the freshly
updated first-player iterate. -/
noncomputable def alternatingRun (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F) (η : ℝ)
    (x₀ : E) (y₀ : F) : ℕ → E × F
  | 0 => (x₀, y₀)
  | k + 1 =>
      let z := alternatingRun DX DY ψX ψY A η x₀ y₀ k
      let x := mirrorStep DX ψX η (A.adjoint z.2) z.1
      (x, mirrorStep DY ψY η (-A x) z.2)

/-- The compact Legendre assumptions supply primal minimization trajectories
for every horizon, so the trajectory premise of the regret theorem is inhabited.
No iterated interiority or primal/dual correspondence is assumed. -/
theorem exists_alternating_primal_trajectories
    (DX : Set E) (DY : Set F) (ψX : E → ℝ) (ψY : F → ℝ)
    (A : E →L[ℝ] F) (η : ℝ) (x₀ : E) (y₀ : F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hlscX : LowerSemicontinuousOn ψX DX) (hlscY : LowerSemicontinuousOn ψY DY)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z)
    (hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (hx₀ : x₀ ∈ intrinsicInterior ℝ DX) (hy₀ : y₀ ∈ intrinsicInterior ℝ DY)
    (hdualX : Differentiable ℝ (Duality.conjugate DX ψX))
    (hdualY : Differentiable ℝ (Duality.conjugate DY ψY)) :
    ∃ (x : ℕ → E) (y : ℕ → F), x 0 = x₀ ∧ y 0 = y₀ ∧
      ∀ T, IsPrimalMirrorTrajectory DX ψX η (fun k => A.adjoint (y k)) x T ∧
        IsPrimalMirrorTrajectory DY ψY η (fun k => -A (x (k + 1))) y T := by
  let x : ℕ → E := fun k => (alternatingRun DX DY ψX ψY A η x₀ y₀ k).1
  let y : ℕ → F := fun k => (alternatingRun DX DY ψX ψY A η x₀ y₀ k).2
  have hxstep (k : ℕ) : x (k + 1) = mirrorStep DX ψX η (A.adjoint (y k)) (x k) := rfl
  have hystep (k : ℕ) : y (k + 1) = mirrorStep DY ψY η (-A (x (k + 1))) (y k) := rfl
  refine ⟨x, y, rfl, rfl, ?_⟩
  intro T
  constructor
  · refine ⟨hx₀, ?_, ?_⟩
    · intro k _hk
      rw [hxstep]
      exact intrinsicInterior_subset
        (mirrorStep_spec hcompactX hlscX hψX hdiffX hsteepX hx₀ hdualX).1
    · intro k _hk c hc
      rw [hxstep]
      exact (mirrorStep_spec hcompactX hlscX hψX hdiffX hsteepX hx₀ hdualX).2.1 hc
  · refine ⟨hy₀, ?_, ?_⟩
    · intro k _hk
      rw [hystep]
      exact intrinsicInterior_subset
        (mirrorStep_spec hcompactY hlscY hψY hdiffY hsteepY hy₀ hdualY).1
    · intro k _hk c hc
      rw [hystep]
      exact (mirrorStep_spec hcompactY hlscY hψY hdiffY hsteepY hy₀ hdualY).2.1 hc

end AltOMD.LegendreTrajectory
