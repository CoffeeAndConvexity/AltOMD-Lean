import AltOMD.Entropy.ExtendedDuality
import AltOMD.VerifiedRegret
import AltOMD.Regret.Decomposition

/-!
# The main regret theorem for extended-real Legendre regularizers

The source radius is an extended-real sum of comparator suprema. Finiteness
forces the effective domains to equal the compact feasible sets. The real
restrictions, finite conjugates, and primal real inequalities are then derived.
-/

open Set Filter
open scoped Topology InnerProductSpace ContDiff

namespace AltOMD.ExtendedRegret

open ExtendedDuality

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The proper closed convex and relative Legendre conditions in the paper. -/
structure IsLegendre (ψ : E → EReal) : Prop where
  proper : Proper ψ
  closed : LowerSemicontinuous ψ
  convex : ExtendedDuality.Convex ψ
  strictConvex : StrictConvexOn ℝ (intrinsicInterior ℝ (domain ψ)) (value ψ)
  c1 : ∀ z ∈ intrinsicInterior ℝ (domain ψ),
    ContDiffAt ℝ 1
      (fun v : (affineSpan ℝ (domain ψ)).direction => value ψ (z + (v : E))) 0
  steep : LegendreBoundary.GradientBlowsUpAtBoundary (domain ψ) (value ψ)

/-- The comparator supremum includes all feasible points, including points
outside the effective domain, where the divergence is infinite. -/
noncomputable def radius (ψ : E → EReal) (D : Set E) (x : E) : EReal :=
  ⨆ c : D, ExtendedDuality.bregman ψ c x

noncomputable def initialRadius (ψX : E → EReal) (DX : Set E)
    (ψY : F → EReal) (DY : Set F) (x₀ : E) (y₀ : F) : EReal :=
  radius ψX DX x₀ + radius ψY DY y₀

theorem radius_nonneg {ψ : E → EReal} {D : Set E} (hp : Proper ψ) {x : E}
    (hx : x ∈ domain ψ) (hxD : x ∈ D) : 0 ≤ radius ψ D x := by
  have h := le_iSup (fun c : D => ExtendedDuality.bregman ψ c x) ⟨x, hxD⟩
  simpa only [radius, bregman_self hp hx] using h

/-- Finite radius excludes every feasible point of infinite regularizer value. -/
theorem subset_domain_of_radius_finite {ψ : E → EReal} {D : Set E} {x : E}
    (hr : radius ψ D x < ⊤) : D ⊆ domain ψ := by
  intro c hc
  by_contra h
  have hb := le_iSup (fun c : D => ExtendedDuality.bregman ψ c x) ⟨c, hc⟩
  rw [bregman_of_not_mem h] at hb
  exact (not_lt_of_ge hb) hr

theorem domain_eq_of_radius_finite {ψ : E → EReal} {D : Set E} {x : E}
    (hclosure : closure (domain ψ) = D) (hr : radius ψ D x < ⊤) : domain ψ = D := by
  apply Set.Subset.antisymm
  · intro c hc
    rw [← hclosure]
    exact subset_closure hc
  · exact subset_domain_of_radius_finite hr

/-- Each comparator supremum is finite when their source sum is finite. -/
theorem radius_finite_of_initialRadius_finite
    {ψX : E → EReal} {DX : Set E} {ψY : F → EReal} {DY : Set F}
    (hpX : Proper ψX) (hpY : Proper ψY) {x₀ : E} {y₀ : F}
    (hx : x₀ ∈ domain ψX) (hy : y₀ ∈ domain ψY)
    (hxD : x₀ ∈ DX) (hyD : y₀ ∈ DY)
    (hR : initialRadius ψX DX ψY DY x₀ y₀ < ⊤) :
    radius ψX DX x₀ < ⊤ ∧ radius ψY DY y₀ < ⊤ := by
  have hxbot : radius ψX DX x₀ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (radius_nonneg hpX hx hxD)
  have hybot : radius ψY DY y₀ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (radius_nonneg hpY hy hyD)
  constructor
  · apply lt_top_iff_ne_top.mpr
    intro h
    have := hR
    rw [initialRadius, h, EReal.top_add_of_ne_bot hybot] at this
    exact lt_irrefl _ this
  · apply lt_top_iff_ne_top.mpr
    intro h
    have := hR
    rw [initialRadius, h, EReal.add_top_of_ne_bot hxbot] at this
    exact lt_irrefl _ this

theorem real_radius_bddAbove {ψ : E → EReal} {D : Set E} {x : E}
    (hp : Proper ψ) (hD : D ⊆ domain ψ) (hr : radius ψ D x < ⊤)
    (hx : x ∈ domain ψ) (hxD : x ∈ D) :
    BddAbove ((fun c => Duality.bregman (value ψ)
      (gradientWithin (value ψ) (domain ψ) x) c x) '' D) := by
  have hbot : radius ψ D x ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (radius_nonneg hp hx hxD)
  refine ⟨(radius ψ D x).toReal, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hr.ne hbot, ← bregman_eq_coe hp (hD hc)]
  exact le_iSup (fun c : D => ExtendedDuality.bregman ψ c x) ⟨c, hc⟩

theorem radius_eq_coe_sSup {ψ : E → EReal} {D : Set E} {x : E}
    (hp : Proper ψ) (hD : D ⊆ domain ψ) (hr : radius ψ D x < ⊤)
    (hx : x ∈ domain ψ) (hxD : x ∈ D) :
    radius ψ D x =
      ((sSup ((fun c => Duality.bregman (value ψ)
        (gradientWithin (value ψ) (domain ψ) x) c x) '' D) : ℝ) : EReal) := by
  have hb := real_radius_bddAbove hp hD hr hx hxD
  have hbot : radius ψ D x ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (radius_nonneg hp hx hxD)
  have hcoe : ((radius ψ D x).toReal : EReal) = radius ψ D x :=
    EReal.coe_toReal hr.ne hbot
  apply le_antisymm
  · apply iSup_le
    intro c
    rw [bregman_eq_coe hp (hD c.property)]
    exact EReal.coe_le_coe_iff.mpr (le_csSup hb ⟨c, c.property, rfl⟩)
  · rw [← hcoe]
    apply EReal.coe_le_coe_iff.mpr
    apply csSup_le (Set.Nonempty.image _ ⟨x, hxD⟩)
    rintro _ ⟨c, hc, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [hcoe, ← bregman_eq_coe hp (hD hc)]
    exact le_iSup (fun c : D => ExtendedDuality.bregman ψ c x) ⟨c, hc⟩

/-- The primal update with the actual extended-real Bregman objective. -/
structure IsPrimalMirrorTrajectory (ψ : E → EReal) (D : Set E) (η : ℝ)
    (loss x : ℕ → E) (T : ℕ) : Prop where
  initialri : x 0 ∈ intrinsicInterior ℝ (domain ψ)
  next_mem : ∀ k < T, x (k + 1) ∈ D
  minimizes : ∀ k < T, ∀ c ∈ D,
    ((η * ⟪loss k, x (k + 1)⟫_ℝ : ℝ) : EReal) +
        ExtendedDuality.bregman ψ (x (k + 1)) (x k) ≤
      ((η * ⟪loss k, c⟫_ℝ : ℝ) : EReal) + ExtendedDuality.bregman ψ c (x k)

/-- Comparison with the current finite point excludes an infinite next value.
This argument does not require a finite comparator radius or a closed domain. -/
theorem IsPrimalMirrorTrajectory.mem_domain {ψ : E → EReal} {D : Set E} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ} (hrun : IsPrimalMirrorTrajectory ψ D η loss x T)
    (hp : Proper ψ) (hD : domain ψ ⊆ D) : ∀ k ≤ T, x k ∈ domain ψ := by
  intro k
  induction k with
  | zero => intro _; exact intrinsicInterior_subset hrun.initialri
  | succ k ih =>
      intro hk
      have hx := ih (Nat.le_of_succ_le hk)
      have hm := hrun.minimizes k hk (x k) (hD hx)
      rw [bregman_self hp hx, add_zero] at hm
      by_contra hn
      rw [bregman_of_not_mem hn, EReal.coe_add_top] at hm
      exact (not_le_of_gt (EReal.coe_lt_top _)) hm

/-- The literal extended-real primal run induces the real-domain run required
by the duality proof. All iterate finiteness is a consequence of minimization. -/
theorem IsPrimalMirrorTrajectory.toDomain {ψ : E → EReal} {D : Set E} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ} (hrun : IsPrimalMirrorTrajectory ψ D η loss x T)
    (hp : Proper ψ) (hD : domain ψ ⊆ D) :
    LegendreTrajectory.IsPrimalMirrorTrajectory (domain ψ) (value ψ) η loss x T := by
  refine ⟨hrun.initialri, fun k hk => hrun.mem_domain hp hD (k + 1) hk, ?_⟩
  intro k hk c hc
  have h := hrun.minimizes k hk c (hD hc)
  rw [bregman_eq_coe hp (hrun.mem_domain hp hD (k + 1) hk), bregman_eq_coe hp hc,
    ← EReal.coe_add, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

theorem IsPrimalMirrorTrajectory.toReal {ψ : E → EReal} {D : Set E} {η : ℝ}
    {loss x : ℕ → E} {T : ℕ} (hrun : IsPrimalMirrorTrajectory ψ D η loss x T)
    (hp : Proper ψ) (hD : domain ψ = D) :
    LegendreTrajectory.IsPrimalMirrorTrajectory D (value ψ) η loss x T := by
  refine ⟨by simpa only [hD] using hrun.initialri, hrun.next_mem, ?_⟩
  intro k hk c hc
  have hn : x (k + 1) ∈ domain ψ := by rw [hD]; exact hrun.next_mem k hk
  have hc' : c ∈ domain ψ := by rwa [hD]
  have h := hrun.minimizes k hk c hc
  rw [bregman_eq_coe hp hn, bregman_eq_coe hp hc', ← EReal.coe_add,
    ← EReal.coe_add] at h
  simpa only [hD] using EReal.coe_le_coe_iff.mp h

/-- The source main theorem for extended-real regularizers. The only finite
radius premise concerns the actual sum of extended-real comparator suprema.
All restrictions and finite-domain facts needed by the real proof are derived. -/
theorem logarithmic_regret (DX : Set E) (DY : Set F)
    (ψX : E → EReal) (ψY : F → EReal) (A : E →L[ℝ] F)
    (hcompactX : IsCompact DX) (hcompactY : IsCompact DY)
    (hclosureX : closure (domain ψX) = DX) (hclosureY : closure (domain ψY) = DY)
    (hlegX : IsLegendre ψX) (hlegY : IsLegendre ψY)
    (hf : ContDiff ℝ ∞ (realConjugate ψX)) (hg : ContDiff ℝ ∞ (realConjugate ψY))
    {K : ℝ} (hK : 1 ≤ K)
    (hderivative : ∀ r : ℕ, 1 ≤ r →
      (⨆ u : E, (‖iteratedFDeriv ℝ r (realConjugate ψX) u‖ : EReal)) +
        (⨆ w : F, (‖iteratedFDeriv ℝ r (realConjugate ψY) w‖ : EReal)) ≤
          ((K ^ r * r.factorial : ℝ) : EReal))
    (x₀ : E) (y₀ : F)
    (hx₀ : x₀ ∈ intrinsicInterior ℝ (domain ψX))
    (hy₀ : y₀ ∈ intrinsicInterior ℝ (domain ψY))
    (hradius : initialRadius ψX DX ψY DY x₀ y₀ < ⊤)
    (T : ℕ) (hT : 1 ≤ T) (x : ℕ → E) (y : ℕ → F)
    (hxinitial : x 0 = x₀) (hyinitial : y 0 = y₀)
    (hxrun : IsPrimalMirrorTrajectory ψX DX
      (stepSize (BilinearRegret.gameConstant A K) T) (fun k => A.adjoint (y k)) x T)
    (hyrun : IsPrimalMirrorTrajectory ψY DY
      (stepSize (BilinearRegret.gameConstant A K) T) (fun k => -A (x (k + 1))) y T) :
    let Λ₀ := (initialRadius ψX DX ψY DY x₀ y₀).toReal
    let C₀ := BilinearRegret.gameConstant A K
    PrimalRegret.sumRegret DX DY A x y T ≤
        16 * C₀ * Λ₀ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ∧
      16 * C₀ * Λ₀ * ((Nat.log 2 T : ℝ) + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ≤
        16 * C₀ * Λ₀ * (Real.logb 2 T + 2) + ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
  have hxdom := intrinsicInterior_subset hx₀
  have hydom := intrinsicInterior_subset hy₀
  have hxD : x₀ ∈ DX := by rw [← hclosureX]; exact subset_closure hxdom
  have hyD : y₀ ∈ DY := by rw [← hclosureY]; exact subset_closure hydom
  obtain ⟨hrX, hrY⟩ := radius_finite_of_initialRadius_finite
    hlegX.proper hlegY.proper hxdom hydom hxD hyD hradius
  have hDX := domain_eq_of_radius_finite hclosureX hrX
  have hDY := domain_eq_of_radius_finite hclosureY hrY
  have hsubX : DX ⊆ domain ψX := by
    intro z hz
    rwa [hDX]
  have hsubY : DY ⊆ domain ψY := by
    intro z hz
    rwa [hDY]
  have hlscX : LowerSemicontinuousOn (value ψX) DX := by
    simpa only [hDX] using lowerSemicontinuousOn_value hlegX.proper hlegX.closed
  have hlscY : LowerSemicontinuousOn (value ψY) DY := by
    simpa only [hDY] using lowerSemicontinuousOn_value hlegY.proper hlegY.closed
  have hFX : realConjugate ψX = Duality.conjugate DX (value ψX) := by
    funext u
    have hfin := ConjugateFeasibility.conjugate_finite ⟨x₀, hxD⟩ hcompactX hlscX u
    rw [realConjugate, conjugate_eq_coe hlegX.proper (by simpa only [hDX] using hfin),
      EReal.toReal_coe, hDX]
  have hGY : realConjugate ψY = Duality.conjugate DY (value ψY) := by
    funext w
    have hfin := ConjugateFeasibility.conjugate_finite ⟨y₀, hyD⟩ hcompactY hlscY w
    rw [realConjugate, conjugate_eq_coe hlegY.proper (by simpa only [hDY] using hfin),
      EReal.toReal_coe, hDY]
  have hd : ∀ r, 1 ≤ r → ∀ u w,
      ‖iteratedFDeriv ℝ r (Duality.conjugate DX (value ψX)) u‖ +
        ‖iteratedFDeriv ℝ r (Duality.conjugate DY (value ψY)) w‖ ≤ K ^ r * r.factorial := by
    intro r hr u w
    rw [← hFX, ← hGY]
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_add]
    exact (add_le_add (le_iSup (fun u : E =>
      (‖iteratedFDeriv ℝ r (realConjugate ψX) u‖ : EReal)) u)
      (le_iSup (fun w : F => (‖iteratedFDeriv ℝ r (realConjugate ψY) w‖ : EReal)) w)).trans
      (hderivative r hr)
  have hΛ : (initialRadius ψX DX ψY DY x₀ y₀).toReal =
      sSup ((fun c => Duality.bregman (value ψX)
        (gradientWithin (value ψX) DX x₀) c x₀) '' DX) +
      sSup ((fun c => Duality.bregman (value ψY)
        (gradientWithin (value ψY) DY y₀) c y₀) '' DY) := by
    rw [initialRadius, radius_eq_coe_sSup hlegX.proper hsubX hrX hxdom hxD,
      radius_eq_coe_sSup hlegY.proper hsubY hrY hydom hyD,
      ← EReal.coe_add, EReal.toReal_coe, hDX, hDY]
  dsimp only
  rw [hΛ]
  apply VerifiedRegret.logarithmic_regret_source DX DY (value ψX) (value ψY) A
    hcompactX hcompactY hlscX hlscY
    (by simpa only [hDX] using convexOn_value hlegX.proper hlegX.convex)
    (by simpa only [hDY] using convexOn_value hlegY.proper hlegY.convex)
    (by simpa only [hDX] using hlegX.strictConvex)
    (by simpa only [hDY] using hlegY.strictConvex)
    (by rw [← hDX]; exact hlegX.c1)
    (by rw [← hDY]; exact hlegY.c1)
    (by simpa only [hDX] using hlegX.steep)
    (by simpa only [hDY] using hlegY.steep)
    (by simpa only [hFX] using hf) (by simpa only [hGY] using hg) hK hd x₀ y₀
    (by simpa only [hDX] using hx₀) (by simpa only [hDY] using hy₀)
    (by simpa only [hDX] using real_radius_bddAbove hlegX.proper hsubX hrX hxdom hxD)
    (by simpa only [hDY] using real_radius_bddAbove hlegY.proper hsubY hrY hydom hyD)
    T hT x y hxinitial hyinitial (hxrun.toReal hlegX.proper hDX) (hyrun.toReal hlegY.proper hDY)

/-- The literal Fenchel coupling of two extended-real regularizers. -/
noncomputable def coupling (ψX : E → EReal) (ψY : F → EReal)
    (cx : E) (cy : F) (u : E) (w : F) : EReal :=
  (ψX cx + conjugate ψX u - (⟪u, cx⟫_ℝ : EReal)) +
    (ψY cy + conjugate ψY w - (⟪w, cy⟫_ℝ : EReal))

noncomputable def energy (ψX : E → EReal) (ψY : F → EReal) (u : E) (w : F) : ℝ :=
  realConjugate ψX u + realConjugate ψY w

theorem coupling_eq_coe {ψX : E → EReal} {ψY : F → EReal}
    (hpX : Proper ψX) (hpY : Proper ψY) {cx u : E} {cy w : F}
    (hcx : cx ∈ domain ψX) (hcy : cy ∈ domain ψY)
    (hu : u ∈ Duality.dualDomain (domain ψX) (value ψX))
    (hw : w ∈ Duality.dualDomain (domain ψY) (value ψY)) :
    coupling ψX ψY cx cy u w =
      (Comparator.coupling (domain ψX) (domain ψY) (value ψX) (value ψY)
        cx cy u w : EReal) := by
  simp only [coupling, Comparator.coupling, Duality.fenchelCoupling,
    ← coe_value hpX hcx, ← coe_value hpY hcy,
    conjugate_eq_coe hpX hu, conjugate_eq_coe hpY hw, EReal.coe_add, EReal.coe_sub]

theorem energy_eq {ψX : E → EReal} {ψY : F → EReal}
    (hpX : Proper ψX) (hpY : Proper ψY) {u : E} {w : F}
    (hu : u ∈ Duality.dualDomain (domain ψX) (value ψX))
    (hw : w ∈ Duality.dualDomain (domain ψY) (value ψY)) :
    energy ψX ψY u w =
      Comparator.energy (domain ψX) (domain ψY) (value ψX) (value ψY) u w := by
  simp only [energy, realConjugate, conjugate_eq_coe hpX hu,
    conjugate_eq_coe hpY hw, EReal.toReal_coe, Comparator.energy]

/-- The complete source decomposition for literal extended-real regularizers.
No finite-radius, compact-domain, or conjugate-smoothness assumption is needed.
Primal minimization proves the finiteness of every generated primal and dual
point. The dual initialization uses the canonical relative gradients. -/
theorem regret_decomposition_all (DX : Set E) (DY : Set F)
    (ψX : E → EReal) (ψY : F → EReal) (A : E →L[ℝ] F) (η : ℝ)
    (hclosureX : closure (domain ψX) = DX) (hclosureY : closure (domain ψY) = DY)
    (hlegX : IsLegendre ψX) (hlegY : IsLegendre ψY)
    (x : ℕ → E) (y : ℕ → F)
    (hxrun : ∀ T, IsPrimalMirrorTrajectory ψX DX η (fun k => A.adjoint (y k)) x T)
    (hyrun : ∀ T, IsPrimalMirrorTrajectory ψY DY η (fun k => -A (x (k + 1))) y T)
    (cx : E) (cy : F) (hcx : cx ∈ domain ψX) (hcy : cy ∈ domain ψY) :
    let u := Decomposition.dualCoordinates (domain ψX) (value ψX) η
      (fun k => A.adjoint (y k)) (x 0)
    let w := Decomposition.dualCoordinates (domain ψY) (value ψY) η
      (fun k => -A (x (k + 1))) (y 0)
    (∀ k,
      conjugate ψX (u k) < ⊤ ∧ conjugate ψY (w k) < ⊤ ∧
      0 ≤ coupling ψX ψY cx cy (u k) (w k) ∧
      coupling ψX ψY cx cy (u k) (w k) =
        ExtendedDuality.bregman ψX cx (x k) + ExtendedDuality.bregman ψY cy (y k)) ∧
    (∀ k,
      ((η * (⟪A (x (k + 1)), cy⟫_ℝ - ⟪A cx, y k⟫_ℝ) : ℝ) : EReal) =
        ((energy ψX ψY (u (k + 1)) (w (k + 1)) - energy ψX ψY (u k) (w k) : ℝ) : EReal) +
        coupling ψX ψY cx cy (u k) (w k) -
          coupling ψX ψY cx cy (u (k + 1)) (w (k + 1))) := by
  have hsubX : domain ψX ⊆ DX := by
    intro z hz; rw [← hclosureX]; exact subset_closure hz
  have hsubY : domain ψY ⊆ DY := by
    intro z hz; rw [← hclosureY]; exact subset_closure hz
  have hdiffX : ∀ z ∈ intrinsicInterior ℝ (domain ψX),
      DifferentiableWithinAt ℝ (value ψX) (domain ψX) z := by
    intro z hz
    exact differentiableWithinAt_of_affineChart (intrinsicInterior_subset hz)
      ((hlegX.c1 z hz).differentiableAt (by norm_num))
  have hdiffY : ∀ z ∈ intrinsicInterior ℝ (domain ψY),
      DifferentiableWithinAt ℝ (value ψY) (domain ψY) z := by
    intro z hz
    exact differentiableWithinAt_of_affineChart (intrinsicInterior_subset hz)
      ((hlegY.c1 z hz).differentiableAt (by norm_num))
  have hrunX := fun T => (hxrun T).toDomain hlegX.proper hsubX
  have hrunY := fun T => (hyrun T).toDomain hlegY.proper hsubY
  have hconvX := convexOn_value hlegX.proper hlegX.convex
  have hconvY := convexOn_value hlegY.proper hlegY.convex
  let u := Decomposition.dualCoordinates (domain ψX) (value ψX) η
    (fun k => A.adjoint (y k)) (x 0)
  let w := Decomposition.dualCoordinates (domain ψY) (value ψY) η
    (fun k => -A (x (k + 1))) (y 0)
  have hfinX : ∀ k, u k ∈ Duality.dualDomain (domain ψX) (value ψX) := by
    intro k
    exact (Decomposition.dualCoordinates_fenchel hconvX hdiffX hlegX.steep
      (hrunX k) k le_rfl).1
  have hfinY : ∀ k, w k ∈ Duality.dualDomain (domain ψY) (value ψY) := by
    intro k
    exact (Decomposition.dualCoordinates_fenchel hconvY hdiffY hlegY.steep
      (hrunY k) k le_rfl).1
  have h := Decomposition.regret_decomposition_all (domain ψX) (domain ψY)
    (value ψX) (value ψY) A η hconvX hconvY hdiffX hdiffY hlegX.steep hlegY.steep
    x y hrunX hrunY cx cy hcx hcy
  change (∀ k, _ ∧ _ ∧ _ ∧ _) ∧ (∀ k, _)
  constructor
  · intro k
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [conjugate_eq_coe hlegX.proper (hfinX k)]
      exact EReal.coe_lt_top _
    · rw [conjugate_eq_coe hlegY.proper (hfinY k)]
      exact EReal.coe_lt_top _
    · rw [coupling_eq_coe hlegX.proper hlegY.proper hcx hcy (hfinX k) (hfinY k)]
      exact EReal.coe_nonneg.mpr (h.1 k).1
    · rw [coupling_eq_coe hlegX.proper hlegY.proper hcx hcy (hfinX k) (hfinY k),
        bregman_eq_coe hlegX.proper hcx, bregman_eq_coe hlegY.proper hcy,
        ← EReal.coe_add]
      congr 1
      rw [Decomposition.bregman_eq_relativeGradient hcx
        ((hxrun k).mem_domain hlegX.proper hsubX k le_rfl),
        Decomposition.bregman_eq_relativeGradient hcy
        ((hyrun k).mem_domain hlegY.proper hsubY k le_rfl)]
      exact (h.1 k).2
  · intro k
    rw [energy_eq hlegX.proper hlegY.proper (hfinX (k + 1)) (hfinY (k + 1)),
      energy_eq hlegX.proper hlegY.proper (hfinX k) (hfinY k),
      coupling_eq_coe hlegX.proper hlegY.proper hcx hcy (hfinX k) (hfinY k),
      coupling_eq_coe hlegX.proper hlegY.proper hcx hcy (hfinX (k + 1)) (hfinY (k + 1)),
      ← EReal.coe_add, ← EReal.coe_sub]
    exact congrArg (fun r : ℝ => (r : EReal)) (h.2 k)

end AltOMD.ExtendedRegret
