import AltOMD.Entropy.Duality
import AltOMD.Regret.Regret
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring

/-!
# The AltOMD comparator identity

The coupling identity is derived from the actual two sequential dual updates,
using the adjoint of the game operator. Its nonnegativity and its initial
Bregman representation are consequences of the analytic duality results.
-/

open scoped InnerProductSpace
open Finset

namespace AltOMD.Comparator

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def energy (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (u : E) (w : F) : ℝ :=
  Duality.conjugate DX ψX u + Duality.conjugate DY ψY w

noncomputable def coupling (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (cx : E) (cy : F) (u : E) (w : F) : ℝ :=
  Duality.fenchelCoupling DX ψX cx u + Duality.fenchelCoupling DY ψY cy w

/-- The combined comparator cost of one alternating update. -/
def cost (A : E →L[ℝ] F) (cx : E) (cy : F) (xnext : E) (y : F) : ℝ :=
  ⟪A xnext, cy⟫_ℝ - ⟪A cx, y⟫_ℝ

/-- Exact one-step comparator identity, derived from the two dual updates. -/
theorem one_step_identity (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (cx : E) (cy : F) (u unext xnext : E) (w wnext y : F) (η : ℝ)
    (hu : unext = u - η • A.adjoint y)
    (hw : wnext = w + η • A xnext) :
    η * cost A cx cy xnext y =
      energy DX DY ψX ψY unext wnext - energy DX DY ψX ψY u w +
        coupling DX DY ψX ψY cx cy u w -
        coupling DX DY ψX ψY cx cy unext wnext := by
  subst unext
  subst wnext
  simp only [cost, energy, coupling, Duality.fenchelCoupling,
    inner_sub_left, inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm (A cx) y]
  ring

/-- The same identity with the primal points defined by the conjugate gradients. -/
theorem altomd_one_step_identity (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (cx : E) (cy : F) (u unext : E) (w wnext : F) (η : ℝ)
    (hu : unext = u - η • A.adjoint (gradient (Duality.conjugate DY ψY) w))
    (hw : wnext = w + η • A (gradient (Duality.conjugate DX ψX) unext)) :
    η * cost A cx cy (gradient (Duality.conjugate DX ψX) unext)
        (gradient (Duality.conjugate DY ψY) w) =
      energy DX DY ψX ψY unext wnext - energy DX DY ψX ψY u w +
        coupling DX DY ψX ψY cx cy u w -
        coupling DX DY ψX ψY cx cy unext wnext :=
  one_step_identity DX DY ψX ψY A cx cy u unext _ w wnext _ η hu hw

theorem coupling_nonneg {DX : Set E} {DY : Set F}
    {ψX : E → ℝ} {ψY : F → ℝ} {cx u : E} {cy w : F}
    (hcx : cx ∈ DX) (hcy : cy ∈ DY)
    (hu : u ∈ Duality.dualDomain DX ψX) (hw : w ∈ Duality.dualDomain DY ψY) :
    0 ≤ coupling DX DY ψX ψY cx cy u w :=
  add_nonneg (Duality.fenchelCoupling_nonneg hu hcx)
    (Duality.fenchelCoupling_nonneg hw hcy)

theorem coupling_eq_bregman {DX : Set E} {DY : Set F}
    {ψX : E → ℝ} {ψY : F → ℝ} {cx u x gx : E} {cy w y gy : F}
    (hψX : ConvexOn ℝ DX ψX) (hψY : ConvexOn ℝ DY ψY)
    (hx : x ∈ intrinsicInterior ℝ DX) (hy : y ∈ intrinsicInterior ℝ DY)
    (hXderiv : HasFDerivWithinAt ψX (innerSL ℝ gx) DX x)
    (hYderiv : HasFDerivWithinAt ψY (innerSL ℝ gy) DY y)
    (hu : u ∈ Duality.dualDomain DX ψX) (hw : w ∈ Duality.dualDomain DY ψY)
    (hXdual : HasFDerivAt (Duality.conjugate DX ψX) (innerSL ℝ x) u)
    (hYdual : HasFDerivAt (Duality.conjugate DY ψY) (innerSL ℝ y) w)
    (hcx : cx ∈ DX) (hcy : cy ∈ DY) :
    coupling DX DY ψX ψY cx cy u w =
      Duality.bregman ψX gx cx x + Duality.bregman ψY gy cy y := by
  unfold coupling
  rw [Duality.fenchelCoupling_eq_bregman hψX hx hXderiv hu hXdual hcx,
    Duality.fenchelCoupling_eq_bregman hψY hy hYderiv hw hYdual hcy]

/-- Telescoping along the actual alternating dual trajectory. -/
theorem trajectory_identity (DX : Set E) (DY : Set F)
    (ψX : E → ℝ) (ψY : F → ℝ) (A : E →L[ℝ] F)
    (cx : E) (cy : F) (u : ℕ → E) (w : ℕ → F) (η : ℝ) (T : ℕ)
    (hu : ∀ k < T, u (k + 1) = u k -
      η • A.adjoint (gradient (Duality.conjugate DY ψY) (w k)))
    (hw : ∀ k < T, w (k + 1) = w k +
      η • A (gradient (Duality.conjugate DX ψX) (u (k + 1)))) :
    η * (∑ k ∈ range T, cost A cx cy
      (gradient (Duality.conjugate DX ψX) (u (k + 1)))
      (gradient (Duality.conjugate DY ψY) (w k))) =
      energy DX DY ψX ψY (u T) (w T) - energy DX DY ψX ψY (u 0) (w 0) +
        coupling DX DY ψX ψY cx cy (u 0) (w 0) -
        coupling DX DY ψX ψY cx cy (u T) (w T) := by
  exact AltOMD.comparator_sum_identity
    (fun (_ : Unit) k => cost A cx cy
      (gradient (Duality.conjugate DX ψX) (u (k + 1)))
      (gradient (Duality.conjugate DY ψY) (w k)))
    (fun k => energy DX DY ψX ψY (u k) (w k))
    (fun (_ : Unit) k => coupling DX DY ψX ψY cx cy (u k) (w k)) η T
    (fun _ k hk => altomd_one_step_identity DX DY ψX ψY A cx cy
      (u k) (u (k + 1)) (w k) (w (k + 1)) η (hu k hk) (hw k hk)) ()

end AltOMD.Comparator
