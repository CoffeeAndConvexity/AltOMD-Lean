import AltOMD.Entropy.Shannon
import AltOMD.Entropy.Shannon.Regret
import AltOMD.Regret.PrimalRegret
import AltOMD.Regret.LegendreTrajectory

/-!
# Concrete Shannon mirror trajectories

The relative Bregman divergence uses mathlib's actual `gradientWithin`.
A normalized multiplicative-weights step is exactly a primal mirror minimizer.
-/

open Set
open scoped BigOperators InnerProductSpace

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private theorem ambientGradient_stationarity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {s : Set E} {x g c : E} (hconv : ConvexOn ℝ s f)
    (hx : x ∈ intrinsicInterior ℝ s) (hg : HasFDerivAt f (innerSL ℝ g) x)
    (hc : c ∈ s) : ⟪g - gradientWithin f s x, c - x⟫_ℝ = 0 := by
  have hdiff : DifferentiableWithinAt ℝ f s x := hg.differentiableAt.differentiableWithinAt
  apply Duality.relative_stationarity hx hdiff.hasGradientWithinAt.hasFDerivWithinAt _ hc
  intro y hy
  have h := Duality.supporting_inequality hconv (intrinsicInterior_subset hx) hy
    hg.hasFDerivWithinAt
  simp only [innerSL_apply_apply, inner_sub_right] at h
  linarith only [h]

/-- The actual within-simplex gradient and the ambient entropy gradient agree
on every feasible difference. -/
theorem entropyGradient_stationarity {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) {c : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) :
    ⟪entropyGradient x - gradientWithin entropy simplex x, c - x⟫_ℝ = 0 :=
  ambientGradient_stationarity convexOn_entropy (positive_mem_intrinsicInterior hx hpos)
    (entropy_hasFDerivAt hpos) hc

/-- The relative-gradient Bregman divergence equals the ambient formula. -/
theorem bregman_eq_entropyGradient {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    Duality.bregman entropy (gradientWithin entropy simplex x) c x =
      Duality.bregman entropy (entropyGradient x) c x := by
  have h := entropyGradient_stationarity hx hpos hc
  simp only [inner_sub_left] at h
  simp only [Duality.bregman]
  linarith

/-- KL is the actual relative Bregman divergence, also at boundary comparators. -/
theorem bregman_eq_kl {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    Duality.bregman entropy (gradientWithin entropy simplex x) c x = kl c x := by
  rw [bregman_eq_entropyGradient hc hx hpos, bregman_entropyGradient_eq_kl hc hx hpos]

/-- The concrete comparator radius for the relative Shannon mirror. -/
theorem bregman_le_radius {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    Duality.bregman entropy (gradientWithin entropy simplex x) c x ≤
      Real.log (1 / minCoordinate x) := by
  rw [bregman_eq_entropyGradient hc hx hpos]
  exact bregman_entropyGradient_le_radius hc hx hpos

/-- The supremum over all simplex comparators obeys the manuscript radius bound. -/
theorem supremum_bregman_le_radius {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    sSup (Set.range (fun c : (simplex : Set (EuclideanSpace ℝ ι)) =>
      Duality.bregman entropy (gradientWithin entropy simplex x) c x)) ≤
      Real.log (1 / minCoordinate x) := by
  apply csSup_le
  · exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact bregman_le_radius c.property hx hpos

/-- Uniform initialization bounds the relative Bregman divergence by `log card`. -/
theorem bregman_uniform_le {c : EuclideanSpace ℝ ι} (hc : c ∈ simplex) :
    Duality.bregman entropy (gradientWithin entropy simplex uniform) c uniform ≤
      Real.log (Fintype.card ι : ℝ) := by
  simpa only [radius_uniform] using bregman_le_radius hc uniform_mem_simplex uniform_pos

/-- Logarithmic coordinates are a representative of the relative entropy gradient. -/
theorem log_stationarity {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) {c : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) :
    ⟪WithLp.toLp 2 (fun i => Real.log (x i)) - gradientWithin entropy simplex x,
      c - x⟫_ℝ = 0 := by
  have h := entropyGradient_stationarity hx hpos hc
  have hnormal :
      ⟪WithLp.toLp 2 (fun i => Real.log (x i)) - entropyGradient x, c - x⟫_ℝ = 0 := by
    simp only [PiLp.inner_apply, Real.inner_apply, PiLp.sub_apply,
      PiLp.toLp_apply, entropyGradient_apply]
    calc
      ∑ i, (Real.log (x i) - (1 + Real.log (x i))) * (c i - x i) =
          -((∑ i, c i) - ∑ i, x i) := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hc.2, hx.2]; ring
  simp only [inner_sub_left] at hnormal h ⊢
  linarith

/-- The normalized update minimizes the exact primal mirror objective. -/
theorem multiplicativeWeights_minimizes {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) (a : EuclideanSpace ℝ ι) (η : ℝ)
    {c : EuclideanSpace ℝ ι} (hc : c ∈ simplex) :
    η * ⟪a, multiplicativeWeights x a η⟫_ℝ +
        Duality.bregman entropy (gradientWithin entropy simplex x) (multiplicativeWeights x a η) x ≤
      η * ⟪a, c⟫_ℝ + Duality.bregman entropy (gradientWithin entropy simplex x) c x := by
  rw [multiplicativeWeights_eq_softmax hx hpos]
  apply PrimalDualStep.mirror_step_minimizes_of_attains
    (mem_dualDomain _) (fun c hc => log_stationarity hx hpos hc)
    (softmax_mem_simplex _) _ hc
  rw [conjugate_eq_logSumExp, conjugate_objective_softmax]

/-- A feasible point minimizes the Shannon mirror objective exactly when it is
its normalized multiplicative-weights update. -/
theorem minimizes_iff_multiplicativeWeights {x y : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) (hy : y ∈ simplex)
    (a : EuclideanSpace ℝ ι) (η : ℝ) :
    (∀ c ∈ simplex, η * ⟪a, y⟫_ℝ +
      Duality.bregman entropy (gradientWithin entropy simplex x) y x ≤
      η * ⟪a, c⟫_ℝ + Duality.bregman entropy (gradientWithin entropy simplex x) c x) ↔
      y = multiplicativeWeights x a η := by
  constructor
  · intro hmin
    have h := PrimalDualStep.mirror_step_gradient_update_of_stationarity mem_dualDomain
      (fun c hc => log_stationarity hx hpos hc) hy
      (by rw [conjugate_eq_logSumExp]; exact (logSumExp_hasFDerivAt _).differentiableAt) hmin
    rw [gradient_conjugate] at h
    exact h.symm.trans (multiplicativeWeights_eq_softmax hx hpos a η).symm
  · rintro rfl
    exact fun c hc => multiplicativeWeights_minimizes hx hpos a η hc

/-- Every primal Shannon mirror step obeys the explicit multiplicative update. -/
theorem IsMirrorTrajectory.multiplicativeWeights_step
    {x loss : ℕ → EuclideanSpace ℝ ι} {η : ℝ} {T : ℕ}
    (h : PrimalRegret.IsMirrorTrajectory simplex entropy η loss x T) :
    ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (loss k) η := by
  intro k hk
  exact (minimizes_iff_multiplicativeWeights (intrinsicInterior_subset (h.interior k hk))
    (positive_of_mem_intrinsicInterior (h.interior k hk)) (h.next_mem k hk) _ _).mp
    (h.minimizes k hk)

/-- The explicit update equations produce the primal trajectories used by the
regret theorem; interior preservation follows from positive weights. -/
theorem multiplicativeWeights_isMirrorTrajectory {x loss : ℕ → EuclideanSpace ℝ ι}
    {η : ℝ} {T : ℕ} (hx0 : x 0 ∈ simplex) (hpos0 : ∀ i, 0 < x 0 i)
    (hstep : ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (loss k) η) :
    PrimalRegret.IsMirrorTrajectory simplex entropy η loss x T := by
  have hm := multiplicativeWeights_trajectory_mem hx0 hpos0 hstep
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact positive_mem_intrinsicInterior (hm k hk.le).1 (hm k hk.le).2
  · intro k hk
    exact (entropy_hasFDerivAt (hm k hk.le).2).differentiableAt.differentiableWithinAt
  · intro k hk
    exact (hm (k + 1) (by omega)).1
  · intro k hk c hc
    rw [hstep k hk]
    exact multiplicativeWeights_minimizes (hm k hk.le).1 (hm k hk.le).2 _ _ hc

/-- The explicit normalized updates and the generic Shannon mirror trajectory
are equivalent for the same positive initial state. -/
theorem isMirrorTrajectory_iff_multiplicativeWeights
    {x loss : ℕ → EuclideanSpace ℝ ι} {η : ℝ} {T : ℕ}
    (hx0 : x 0 ∈ simplex) (hpos0 : ∀ i, 0 < x 0 i) :
    PrimalRegret.IsMirrorTrajectory simplex entropy η loss x T ↔
      ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (loss k) η :=
  ⟨IsMirrorTrajectory.multiplicativeWeights_step,
    multiplicativeWeights_isMirrorTrajectory hx0 hpos0⟩

/-- The same update equations satisfy the minimal primal trajectory interface. -/
theorem multiplicativeWeights_isPrimalMirrorTrajectory {x loss : ℕ → EuclideanSpace ℝ ι}
    {η : ℝ} {T : ℕ} (hx0 : x 0 ∈ simplex) (hpos0 : ∀ i, 0 < x 0 i)
    (hstep : ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (loss k) η) :
    LegendreTrajectory.IsPrimalMirrorTrajectory simplex entropy η loss x T := by
  have hrun := multiplicativeWeights_isMirrorTrajectory hx0 hpos0 hstep
  exact ⟨positive_mem_intrinsicInterior hx0 hpos0, hrun.next_mem, hrun.minimizes⟩

/-- For two uniform initial strategies the sum of radii is `log(nm)`. -/
theorem uniform_pair_radius {κ : Type*} [Fintype κ] [Nonempty κ] :
    Real.log (1 / minCoordinate (uniform : EuclideanSpace ℝ ι)) +
      Real.log (1 / minCoordinate (uniform : EuclideanSpace ℝ κ)) =
        Real.log ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)) := by
  simp only [radius_uniform]
  exact (Real.log_mul (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm

end AltOMD.Shannon
