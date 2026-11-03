import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Compact maximizers used in Banach's theorem for symmetric multilinear forms. -/

open Finset
open scoped BigOperators

namespace AltOMD.Polarization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Nontrivial E]

/-- Among unit tuples attaining the multilinear norm, one maximizes the norm
of the sum of its entries. -/
theorem exists_norm_sum_maximizer {n : ℕ} (M : E [×n]→L[ℝ] ℝ) :
    ∃ v : Fin n → E, (∀ i, ‖v i‖ = 1) ∧ |M v| = ‖M‖ ∧
      ∀ w : Fin n → E, (∀ i, ‖w i‖ = 1) → |M w| = ‖M‖ →
        ‖∑ i, w i‖ ≤ ‖∑ i, v i‖ := by
  classical
  obtain ⟨a, ha⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let S : Set (Fin n → E) := Set.univ.pi (fun _ => Metric.sphere (0 : E) 1)
  have hS_mem (v : Fin n → E) : v ∈ S ↔ ∀ i, ‖v i‖ = 1 := by
    simp [S, Set.mem_pi]
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hS_ne : S.Nonempty := ⟨fun _ => a, (hS_mem _).2 fun _ => ha⟩
  obtain ⟨w, hw, hwmax⟩ := hS.exists_isMaxOn hS_ne M.cont.norm.continuousOn
  have hwunit := (hS_mem w).1 hw
  have hwbound : ‖M w‖ ≤ ‖M‖ := M.unit_le_opNorm
    ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (hwunit i).le)
  have hnorm : ‖M‖ ≤ ‖M w‖ := by
    apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
    intro x
    let y : Fin n → E := fun i => if x i = 0 then a else ‖x i‖⁻¹ • x i
    have hy (i : Fin n) : ‖y i‖ = 1 := by
      by_cases hi : x i = 0
      · simp [y, hi, ha]
      · simp [y, hi, norm_smul, norm_ne_zero_iff.mpr hi]
    have hxy : x = fun i => ‖x i‖ • y i := by
      funext i
      by_cases hi : x i = 0
      · simp [y, hi]
      · simp [y, hi, smul_smul, norm_ne_zero_iff.mpr hi]
    calc
      ‖M x‖ = (∏ i, ‖x i‖) * ‖M y‖ := by
        conv_lhs => rw [hxy]
        rw [M.map_smul_univ, norm_smul]
        simp
      _ ≤ (∏ i, ‖x i‖) * ‖M w‖ :=
        mul_le_mul_of_nonneg_left (hwmax ((hS_mem y).2 hy)) (by positivity)
      _ = ‖M w‖ * ∏ i, ‖x i‖ := mul_comm _ _
  have hweq : ‖M w‖ = ‖M‖ := le_antisymm hwbound hnorm
  let T : Set (Fin n → E) := S ∩ {v | ‖M v‖ = ‖M‖}
  have hT : IsCompact T := hS.inter_right (isClosed_eq M.cont.norm continuous_const)
  have hT_ne : T.Nonempty := ⟨w, hw, hweq⟩
  have hsum : Continuous (fun v : Fin n → E => ‖∑ i, v i‖) := by fun_prop
  obtain ⟨v, hv, hvmax⟩ := hT.exists_isMaxOn hT_ne hsum.continuousOn
  refine ⟨v, (hS_mem v).1 hv.1, ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using hv.2
  · intro z hz hMz
    exact hvmax ⟨(hS_mem z).2 hz,
      by simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using hMz⟩

end AltOMD.Polarization
