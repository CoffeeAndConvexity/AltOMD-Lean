import AltOMD.Regret.LegendreTrajectory
import AltOMD.Regret.Comparator

/-!
# Regret decomposition along actual primal AltOMD trajectories

The primal minimization updates imply that each accumulated dual variable
supports the regularizer at the corresponding primal iterate. Thus conjugate
finiteness, relative stationarity, and the Bregman representation are proved
along the trajectory. No conjugate derivative or pointwise support premise
is required.
-/

open Set
open scoped InnerProductSpace

namespace AltOMD.Decomposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The source dual initialization uses the canonical relative gradient.
The subsequent updates accumulate the actual primal losses. -/
noncomputable def dualCoordinates (D : Set E) (ψ : E → ℝ) (η : ℝ)
    (loss : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => (relativeGradient D ψ x₀ : E)
  | k + 1 => dualCoordinates D ψ η loss x₀ k - η • loss k

/-- The Bregman expression on feasible points uses exactly the relative
gradient, independently of the ambient within-derivative representative. -/
theorem bregman_eq_relativeGradient {D : Set E} {ψ : E → ℝ} {c x : E}
    (hc : c ∈ D) (hx : x ∈ D) :
    Duality.bregman ψ (gradientWithin ψ D x) c x =
      Duality.bregman ψ (relativeGradient D ψ x : E) c x := by
  let v : (affineSpan ℝ D).direction :=
    ⟨c - x, AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ D hc) (subset_affineSpan ℝ D hx)⟩
  have hr := inner_relativeGradient D ψ x v
  change ⟪(relativeGradient D ψ x : E), c - x⟫_ℝ =
    fderivWithin ℝ ψ D x (c - x) at hr
  have hg : ⟪gradientWithin ψ D x, c - x⟫_ℝ =
      fderivWithin ℝ ψ D x (c - x) := by
    change (InnerProductSpace.toDual ℝ E (gradientWithin ψ D x)) (c - x) = _
    rw [toDual_gradientWithin]
  simp only [Duality.bregman, hg, hr]

/-- Every accumulated dual variable supports the regularizer at the actual
primal minimizer. Interior preservation follows from the Legendre condition. -/
theorem dualCoordinates_maximizes {D : Set E} {ψ : E → ℝ} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ}
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hrun : LegendreTrajectory.IsPrimalMirrorTrajectory D ψ η loss x T) :
    ∀ k ≤ T, ∀ c ∈ D,
      ⟪dualCoordinates D ψ η loss (x 0) k, c⟫_ℝ - ψ c ≤
        ⟪dualCoordinates D ψ η loss (x 0) k, x k⟫_ℝ - ψ (x k) := by
  intro k
  induction k with
  | zero =>
      intro _ c hc
      have hx : x 0 ∈ D := intrinsicInterior_subset hrun.initialri
      have hs := Duality.supporting_inequality hψ hx hc
        (hdiff _ hrun.initialri).hasFDerivWithinAt
      let v : (affineSpan ℝ D).direction :=
        ⟨c - x 0, AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ D hc) (subset_affineSpan ℝ D hx)⟩
      have hv := inner_relativeGradient D ψ (x 0) v
      change ⟪(relativeGradient D ψ (x 0) : E), c - x 0⟫_ℝ =
        fderivWithin ℝ ψ D (x 0) (c - x 0) at hv
      rw [← hv] at hs
      simp only [inner_sub_right] at hs
      simpa only [dualCoordinates] using (by linarith :
        ⟪(relativeGradient D ψ (x 0) : E), c⟫_ℝ - ψ c ≤
          ⟪(relativeGradient D ψ (x 0) : E), x 0⟫_ℝ - ψ (x 0))
  | succ k ih =>
      intro hk c hc
      have hkT : k < T := hk
      have hri := hrun.interior hψ hdiff hsteep k (Nat.le_of_lt hkT)
      have hstationary : ∀ a ∈ D,
          ⟪dualCoordinates D ψ η loss (x 0) k -
            gradientWithin ψ D (x k), a - x k⟫_ℝ = 0 := by
        intro a ha
        exact Duality.relative_stationarity hri
          (hdiff _ hri).hasGradientWithinAt.hasFDerivWithinAt
          (ih (Nat.le_of_lt hkT)) ha
      have hm := hrun.minimizes k hkT c hc
      rw [PrimalDualStep.mirror_objective_eq_of_stationarity hstationary
        (hrun.next_mem k hkT),
        PrimalDualStep.mirror_objective_eq_of_stationarity hstationary hc] at hm
      change ⟪dualCoordinates D ψ η loss (x 0) k - η • loss k, c⟫_ℝ - ψ c ≤
        ⟪dualCoordinates D ψ η loss (x 0) k - η • loss k, x (k + 1)⟫_ℝ -
          ψ (x (k + 1))
      linarith

/-- The accumulated dual conjugate is finite and attained at every iterate.
These conclusions also supply the conversion to literal extended-real
Fenchel conjugates on the effective domain. -/
theorem dualCoordinates_fenchel {D : Set E} {ψ : E → ℝ} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ}
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hrun : LegendreTrajectory.IsPrimalMirrorTrajectory D ψ η loss x T) :
    ∀ k ≤ T,
      dualCoordinates D ψ η loss (x 0) k ∈ Duality.dualDomain D ψ ∧
      Duality.conjugate D ψ (dualCoordinates D ψ η loss (x 0) k) =
        ⟪dualCoordinates D ψ η loss (x 0) k, x k⟫_ℝ - ψ (x k) := by
  intro k hk
  have hmem := intrinsicInterior_subset (hrun.interior hψ hdiff hsteep k hk)
  have hmax := dualCoordinates_maximizes hψ hdiff hsteep hrun k hk
  have hfinite : dualCoordinates D ψ η loss (x 0) k ∈ Duality.dualDomain D ψ := by
    refine ⟨⟪dualCoordinates D ψ η loss (x 0) k, x k⟫_ℝ - ψ (x k), ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact hmax c hc
  exact ⟨hfinite, le_antisymm (Duality.conjugate_le ⟨x k, hmem⟩ hmax)
    (Duality.le_conjugate hfinite hmem)⟩

/-- Finiteness and the nonnegative Bregman representation hold at every
iterate, including the terminal point of a finite primal trajectory. -/
theorem mirror_trajectory_coupling {D : Set E} {ψ : E → ℝ} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ}
    (hψ : ConvexOn ℝ D ψ)
    (hdiff : ∀ z ∈ intrinsicInterior ℝ D, DifferentiableWithinAt ℝ ψ D z)
    (hsteep : LegendreBoundary.GradientBlowsUpAtBoundary D ψ)
    (hrun : LegendreTrajectory.IsPrimalMirrorTrajectory D ψ η loss x T) :
    ∀ k ≤ T,
      dualCoordinates D ψ η loss (x 0) k ∈ Duality.dualDomain D ψ ∧
      ∀ c ∈ D,
        0 ≤ Duality.fenchelCoupling D ψ c (dualCoordinates D ψ η loss (x 0) k) ∧
        Duality.fenchelCoupling D ψ c (dualCoordinates D ψ η loss (x 0) k) =
          Duality.bregman ψ (gradientWithin ψ D (x k)) c (x k) := by
  intro k hk
  let u := dualCoordinates D ψ η loss (x 0) k
  have hri := hrun.interior hψ hdiff hsteep k hk
  have hmem : x k ∈ D := intrinsicInterior_subset hri
  have hmax : ∀ c ∈ D, ⟪u, c⟫_ℝ - ψ c ≤ ⟪u, x k⟫_ℝ - ψ (x k) :=
    dualCoordinates_maximizes hψ hdiff hsteep hrun k hk
  have hfinite : u ∈ Duality.dualDomain D ψ := by
    refine ⟨⟪u, x k⟫_ℝ - ψ (x k), ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact hmax c hc
  have hattain : Duality.conjugate D ψ u = ⟪u, x k⟫_ℝ - ψ (x k) :=
    le_antisymm (Duality.conjugate_le ⟨x k, hmem⟩ hmax)
      (Duality.le_conjugate hfinite hmem)
  refine ⟨hfinite, ?_⟩
  intro c hc
  refine ⟨Duality.fenchelCoupling_nonneg hfinite hc, ?_⟩
  have hs := Duality.relative_stationarity hri
    (hdiff _ hri).hasGradientWithinAt.hasFDerivWithinAt hmax hc
  change Duality.fenchelCoupling D ψ c u = _
  simp only [Duality.fenchelCoupling, Duality.bregman, hattain, inner_sub_right]
  simp only [inner_sub_left, inner_sub_right] at hs
  linarith

/-- The complete regret-decomposition lemma for a finite primal AltOMD run.
The dual initialization is the canonical relative gradient, followed by
the actual accumulated losses. All analytic conclusions at later iterates
follow from the stated primal updates and Legendre assumptions. -/
theorem regret_decomposition
    (DX : Set E) (DY : Set F) (ψX : E → ℝ) (ψY : F → ℝ)
    (A : E →L[ℝ] F) (η : ℝ)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z)
    (hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hxrun : LegendreTrajectory.IsPrimalMirrorTrajectory DX ψX η
      (fun k => A.adjoint (y k)) x T)
    (hyrun : LegendreTrajectory.IsPrimalMirrorTrajectory DY ψY η
      (fun k => -A (x (k + 1))) y T)
    (cx : E) (cy : F) (hcx : cx ∈ DX) (hcy : cy ∈ DY) :
    let u := dualCoordinates DX ψX η (fun k => A.adjoint (y k)) (x 0)
    let w := dualCoordinates DY ψY η (fun k => -A (x (k + 1))) (y 0)
    (∀ k ≤ T,
      0 ≤ Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) ∧
      Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) =
        Duality.bregman ψX (relativeGradient DX ψX (x k) : E) cx (x k) +
          Duality.bregman ψY (relativeGradient DY ψY (y k) : F) cy (y k)) ∧
    (∀ k < T,
      η * (⟪A (x (k + 1)), cy⟫_ℝ - ⟪A cx, y k⟫_ℝ) =
        Comparator.energy DX DY ψX ψY (u (k + 1)) (w (k + 1)) -
          Comparator.energy DX DY ψX ψY (u k) (w k) +
        Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) -
          Comparator.coupling DX DY ψX ψY cx cy (u (k + 1)) (w (k + 1))) := by
  dsimp only
  constructor
  · intro k hk
    have hx := (mirror_trajectory_coupling hψX hdiffX hsteepX hxrun k hk).2 cx hcx
    have hy := (mirror_trajectory_coupling hψY hdiffY hsteepY hyrun k hk).2 cy hcy
    refine ⟨add_nonneg hx.1 hy.1, ?_⟩
    have heq := congrArg₂ (· + ·) hx.2 hy.2
    rw [bregman_eq_relativeGradient hcx
      (intrinsicInterior_subset (hxrun.interior hψX hdiffX hsteepX k hk)),
      bregman_eq_relativeGradient hcy
        (intrinsicInterior_subset (hyrun.interior hψY hdiffY hsteepY k hk))] at heq
    exact heq
  · intro k _
    exact Comparator.one_step_identity DX DY ψX ψY A cx cy _ _ _ _ _ _ η rfl
      (by simp only [dualCoordinates, smul_neg, sub_neg_eq_add])

/-- The complete decomposition for every index of an infinite generated run.
The only trajectory inputs are feasible primal minimizers and interior
initialization for every finite horizon. -/
theorem regret_decomposition_all
    (DX : Set E) (DY : Set F) (ψX : E → ℝ) (ψY : F → ℝ)
    (A : E →L[ℝ] F) (η : ℝ)
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hdiffX : ∀ z ∈ intrinsicInterior ℝ DX, DifferentiableWithinAt ℝ ψX DX z)
    (hdiffY : ∀ z ∈ intrinsicInterior ℝ DY, DifferentiableWithinAt ℝ ψY DY z)
    (hsteepX : LegendreBoundary.GradientBlowsUpAtBoundary DX ψX)
    (hsteepY : LegendreBoundary.GradientBlowsUpAtBoundary DY ψY)
    (x : ℕ → E) (y : ℕ → F)
    (hxrun : ∀ T, LegendreTrajectory.IsPrimalMirrorTrajectory DX ψX η
      (fun k => A.adjoint (y k)) x T)
    (hyrun : ∀ T, LegendreTrajectory.IsPrimalMirrorTrajectory DY ψY η
      (fun k => -A (x (k + 1))) y T)
    (cx : E) (cy : F) (hcx : cx ∈ DX) (hcy : cy ∈ DY) :
    let u := dualCoordinates DX ψX η (fun k => A.adjoint (y k)) (x 0)
    let w := dualCoordinates DY ψY η (fun k => -A (x (k + 1))) (y 0)
    (∀ k,
      0 ≤ Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) ∧
      Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) =
        Duality.bregman ψX (relativeGradient DX ψX (x k) : E) cx (x k) +
          Duality.bregman ψY (relativeGradient DY ψY (y k) : F) cy (y k)) ∧
    (∀ k,
      η * (⟪A (x (k + 1)), cy⟫_ℝ - ⟪A cx, y k⟫_ℝ) =
        Comparator.energy DX DY ψX ψY (u (k + 1)) (w (k + 1)) -
          Comparator.energy DX DY ψX ψY (u k) (w k) +
        Comparator.coupling DX DY ψX ψY cx cy (u k) (w k) -
          Comparator.coupling DX DY ψX ψY cx cy (u (k + 1)) (w (k + 1))) := by
  dsimp only
  constructor
  · intro k
    exact (regret_decomposition DX DY ψX ψY A η hψX hψY hdiffX hdiffY
      hsteepX hsteepY k x y (hxrun k) (hyrun k) cx cy hcx hcy).1 k le_rfl
  · intro k
    exact (regret_decomposition DX DY ψX ψY A η hψX hψY hdiffX hdiffY
      hsteepX hsteepY (k + 1) x y (hxrun (k + 1)) (hyrun (k + 1)) cx cy hcx hcy).2
        k (Nat.lt_succ_self k)

end AltOMD.Decomposition
