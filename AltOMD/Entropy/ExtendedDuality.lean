import AltOMD.Entropy.RelativeGradient
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Convex duality for extended-real regularizers

The effective domain and the Fenchel supremum belong to the extended-real
function itself. Real-valued restrictions appear only inside differentiation
and in proved reductions to the real convex-duality library.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace AltOMD.ExtendedDuality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def domain (ψ : E → EReal) : Set E := {x | ψ x < ⊤}

def Proper (ψ : E → EReal) : Prop :=
  (∀ x, ψ x ≠ ⊥) ∧ (domain ψ).Nonempty

def Convex (ψ : E → EReal) : Prop :=
  _root_.Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)}

noncomputable def value (ψ : E → EReal) (x : E) : ℝ := (ψ x).toReal

noncomputable def conjugate (ψ : E → EReal) (u : E) : EReal :=
  ⨆ x : E, (⟪u, x⟫_ℝ : EReal) - ψ x

noncomputable def realConjugate (ψ : E → EReal) (u : E) : ℝ :=
  (conjugate ψ u).toReal

theorem coe_value {ψ : E → EReal} (hp : Proper ψ) {x : E} (hx : x ∈ domain ψ) :
    (value ψ x : EReal) = ψ x := EReal.coe_toReal hx.ne (hp.1 x)

theorem eq_top_of_not_mem {ψ : E → EReal} {x : E} (hx : x ∉ domain ψ) :
    ψ x = ⊤ := top_unique (not_lt.mp hx)

theorem epigraph_eq {ψ : E → EReal} (hp : Proper ψ) :
    {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} =
      {p | p.1 ∈ domain ψ ∧ value ψ p.1 ≤ p.2} := by
  ext p
  change ψ p.1 ≤ (p.2 : EReal) ↔ p.1 ∈ domain ψ ∧ value ψ p.1 ≤ p.2
  constructor
  · intro h
    have hx : p.1 ∈ domain ψ := h.trans_lt (EReal.coe_lt_top _)
    exact ⟨hx, EReal.coe_le_coe_iff.mp (by rwa [coe_value hp hx])⟩
  · rintro ⟨hx, h⟩
    rw [← coe_value hp hx]
    exact EReal.coe_le_coe_iff.mpr h

theorem convexOn_value {ψ : E → EReal} (hp : Proper ψ) (hc : Convex ψ) :
    ConvexOn ℝ (domain ψ) (value ψ) := by
  apply convexOn_of_convex_epigraph
  simpa only [Convex, epigraph_eq hp] using hc

theorem lowerSemicontinuousOn_value {ψ : E → EReal} (hp : Proper ψ)
    (hl : LowerSemicontinuous ψ) : LowerSemicontinuousOn (value ψ) (domain ψ) := by
  intro x hx b hb
  have hb' : (b : EReal) < ψ x := by
    rw [← coe_value hp hx]
    exact EReal.coe_lt_coe_iff.mpr hb
  filter_upwards [(hl x b hb').filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hyD
  apply EReal.coe_lt_coe_iff.mp
  rwa [coe_value hp hyD]

theorem conjugate_ne_bot {ψ : E → EReal} (hp : Proper ψ) (u : E) :
    conjugate ψ u ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hp.2
  have h : ((⟪u, x⟫_ℝ - value ψ x : ℝ) : EReal) ≤ conjugate ψ u := by
    rw [EReal.coe_sub, coe_value hp hx]
    exact le_iSup (fun y => (⟪u, y⟫_ℝ : EReal) - ψ y) x
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h

theorem mem_dualDomain_of_finite {ψ : E → EReal} (hp : Proper ψ) {u : E}
    (hu : conjugate ψ u < ⊤) : u ∈ Duality.dualDomain (domain ψ) (value ψ) := by
  refine ⟨realConjugate ψ u, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply EReal.coe_le_coe_iff.mp
  rw [realConjugate, EReal.coe_toReal hu.ne (conjugate_ne_bot hp u),
    EReal.coe_sub, coe_value hp hx]
  exact le_iSup (fun y => (⟪u, y⟫_ℝ : EReal) - ψ y) x

theorem conjugate_eq_coe {ψ : E → EReal} (hp : Proper ψ) {u : E}
    (hu : u ∈ Duality.dualDomain (domain ψ) (value ψ)) :
    conjugate ψ u = (Duality.conjugate (domain ψ) (value ψ) u : EReal) := by
  have hupper : conjugate ψ u ≤
      (Duality.conjugate (domain ψ) (value ψ) u : EReal) := by
    apply iSup_le
    intro x
    by_cases hx : x ∈ domain ψ
    · rw [← coe_value hp hx, ← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (Duality.le_conjugate hu hx)
    · simp [eq_top_of_not_mem hx]
  have hfinite : conjugate ψ u ≠ ⊤ :=
    (hupper.trans_lt (EReal.coe_lt_top _)).ne
  have hcoe : (realConjugate ψ u : EReal) = conjugate ψ u :=
    EReal.coe_toReal hfinite (conjugate_ne_bot hp u)
  apply le_antisymm hupper
  rw [← hcoe]
  apply EReal.coe_le_coe_iff.mpr
  apply Duality.conjugate_le hp.2
  intro x hx
  apply EReal.coe_le_coe_iff.mp
  rw [hcoe, EReal.coe_sub, coe_value hp hx]
  exact le_iSup (fun y => (⟪u, y⟫_ℝ : EReal) - ψ y) x

theorem realConjugate_eq {ψ : E → EReal} (hp : Proper ψ) {u : E}
    (hu : conjugate ψ u < ⊤) :
    realConjugate ψ u = Duality.conjugate (domain ψ) (value ψ) u := by
  rw [realConjugate, conjugate_eq_coe hp (mem_dualDomain_of_finite hp hu), EReal.toReal_coe]

theorem realConjugate_eventuallyEq {ψ : E → EReal} (hp : Proper ψ) {u : E}
    (hu : ∀ᶠ v in 𝓝 u, conjugate ψ v < ⊤) :
    realConjugate ψ =ᶠ[𝓝 u] Duality.conjugate (domain ψ) (value ψ) :=
  hu.mono fun _ hv => realConjugate_eq hp hv

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The Bregman divergence uses the differential in feasible directions.
Outside the effective domain the comparator value is exactly `+∞`. -/
noncomputable def bregman (ψ : E → EReal) (c x : E) : EReal :=
  ψ c - ((value ψ x + fderivWithin ℝ (value ψ) (domain ψ) x (c - x) : ℝ) : EReal)

theorem bregman_of_not_mem {ψ : E → EReal} {c x : E} (hc : c ∉ domain ψ) :
    bregman ψ c x = ⊤ := by
  unfold bregman
  rw [eq_top_of_not_mem hc]
  exact EReal.top_sub_coe _

theorem bregman_eq_coe {ψ : E → EReal} (hp : Proper ψ) {c x : E}
    (hc : c ∈ domain ψ) :
    bregman ψ c x =
      (Duality.bregman (value ψ) (gradientWithin (value ψ) (domain ψ) x) c x : EReal) := by
  rw [bregman, ← coe_value hp hc, ← EReal.coe_sub]
  congr 1
  simp only [Duality.bregman, inner_gradientWithin_left]
  ring

theorem bregman_self {ψ : E → EReal} (hp : Proper ψ) {x : E} (hx : x ∈ domain ψ) :
    bregman ψ x x = 0 := by
  rw [bregman_eq_coe hp hx]
  simp [Duality.bregman]

theorem inner_relativeGradient_sub {D : Set E} {f : E → ℝ} {x c : E}
    (hx : x ∈ D) (hc : c ∈ D) :
    ⟪(relativeGradient D f x : E), c - x⟫_ℝ =
      ⟪gradientWithin f D x, c - x⟫_ℝ := by
  let v : (affineSpan ℝ D).direction :=
    ⟨c - x, AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ D hc) (subset_affineSpan ℝ D hx)⟩
  change ⟪relativeGradient D f x, v⟫_ℝ = _
  rw [inner_relativeGradient, inner_gradientWithin_left]

/-- The extended-real formulation of the manuscript's Fenchel--Legendre
proposition. Finiteness of the actual conjugate is only required near `u`.
The primal derivative is taken in coordinates on the affine hull. -/
theorem fenchel_legendre_identities (ψ : E → EReal)
    (hp : Proper ψ) (hc : Convex ψ)
    (hdiff : ∀ x ∈ intrinsicInterior ℝ (domain ψ),
      DifferentiableAt ℝ
        (fun v : (affineSpan ℝ (domain ψ)).direction => value ψ (x + (v : E))) 0)
    (u : E) (hfinite : ∀ᶠ v in 𝓝 u, conjugate ψ v < ⊤)
    (hdual : DifferentiableAt ℝ (realConjugate ψ) u)
    (hx : gradient (realConjugate ψ) u ∈ intrinsicInterior ℝ (domain ψ)) :
    let x := gradient (realConjugate ψ) u
    ψ x + conjugate ψ u = (⟪u, x⟫_ℝ : EReal) ∧
      ∀ c ∈ domain ψ,
        ⟪u - (relativeGradient (domain ψ) (value ψ) x : E), c - x⟫_ℝ = 0 := by
  let x := gradient (realConjugate ψ) u
  have hlocal := realConjugate_eventuallyEq hp hfinite
  have hduald : HasFDerivAt (Duality.conjugate (domain ψ) (value ψ))
      (innerSL ℝ x) u :=
    hdual.hasGradientAt.hasFDerivAt.congr_of_eventuallyEq hlocal.symm
  have hprimal : DifferentiableWithinAt ℝ (value ψ) (domain ψ) x :=
    differentiableWithinAt_of_affineChart (intrinsicInterior_subset hx) (hdiff x hx)
  have hu := mem_dualDomain_of_finite hp (hfinite.self_of_nhds)
  obtain ⟨heq, hstat⟩ := Duality.fenchel_legendre_identities (convexOn_value hp hc) hx
    hprimal.hasGradientWithinAt.hasFDerivWithinAt hu hduald
  dsimp only
  constructor
  · rw [← coe_value hp (intrinsicInterior_subset hx), conjugate_eq_coe hp hu,
      ← EReal.coe_add, heq]
  · intro c hc'
    have h := hstat c hc'
    simp only [inner_sub_left] at h ⊢
    rw [inner_relativeGradient_sub (intrinsicInterior_subset hx) hc']
    exact h

end FiniteDimensional

end AltOMD.ExtendedDuality
