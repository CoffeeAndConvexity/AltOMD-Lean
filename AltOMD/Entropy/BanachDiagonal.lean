import AltOMD.Entropy.BanachGeometry
import AltOMD.Entropy.BanachPair

/-! A norm-attaining tuple with maximal sum has equal coordinates. -/

open Finset Function
open scoped BigOperators

namespace AltOMD.Polarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

omit [InnerProductSpace ℝ E] in
private theorem sum_update_eq (v : Fin n → E) (i : Fin n) (x : E) :
    (∑ k, Function.update v i x k) = (∑ k, v k) - v i + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) v (v i)
  rw [Function.update_eq_self] at h
  rw [h]
  abel

omit [InnerProductSpace ℝ E] in
private theorem sum_pairUpdate_eq (v : Fin n → E) {i j : Fin n} (hij : i ≠ j)
    (x y : E) :
    (∑ k, pairUpdate v i j x y k) = (∑ k, v k) - v i - v j + x + y := by
  unfold pairUpdate
  rw [sum_update_eq, sum_update_eq, Function.update_of_ne hij.symm]
  abel

omit [InnerProductSpace ℝ E] in
private theorem unit_update_neg (v : Fin n → E) (hv : ∀ k, ‖v k‖ = 1)
    (i : Fin n) : ∀ k, ‖Function.update v i (-v i) k‖ = 1 := by
  intro k
  by_cases hk : k = i
  · subst k
    simp [hv]
  · simp [Function.update_of_ne hk, hv]

private theorem abs_map_update_neg (M : E [×n]→L[ℝ] ℝ) (v : Fin n → E)
    (i : Fin n) : |M (Function.update v i (-v i))| = |M v| := by
  have h := M.toMultilinearMap.map_update_neg v i (v i)
  change M (Function.update v i (-v i)) = -M (Function.update v i (v i)) at h
  rw [Function.update_eq_self] at h
  rw [h, abs_neg]

/-- Among norm-attaining unit tuples, a tuple whose sum has maximal norm is
diagonal. Sign changes and normalized pair averages preserve norm attainment. -/
theorem norm_sum_maximizer_is_constant (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    (v : Fin n → E) (hv : ∀ k, ‖v k‖ = 1) (hattain : |M v| = ‖M‖)
    (hmax : ∀ w : Fin n → E, (∀ k, ‖w k‖ = 1) → |M w| = ‖M‖ →
      ‖∑ k, w k‖ ≤ ‖∑ k, v k‖) : ∀ i j, v i = v j := by
  intro i j
  by_cases hij : i = j
  · simp [hij]
  let r := (∑ k, v k) - v i - v j
  have hsum : r + v i + v j = ∑ k, v k := by dsimp [r]; abel
  apply eq_of_norm_sum_max (v i) (v j) r (hv i) (hv j)
  · have h := hmax (Function.update v i (-v i)) (unit_update_neg v hv i)
      ((abs_map_update_neg M v i).trans hattain)
    rw [sum_update_eq] at h
    rw [hsum]
    convert h using 1
    congr 1
    dsimp [r]
    abel
  · have h := hmax (Function.update v j (-v j)) (unit_update_neg v hv j)
      ((abs_map_update_neg M v j).trans hattain)
    rw [sum_update_eq] at h
    rw [hsum]
    convert h using 1
    congr 1
    dsimp [r]
    abel
  · let w := Function.update v i (-v i)
    have hw := unit_update_neg v hv i
    have hwj : w j = v j := Function.update_of_ne (Ne.symm hij) _ _
    have h := hmax (Function.update w j (-w j)) (unit_update_neg w hw j)
      ((abs_map_update_neg M w j).trans ((abs_map_update_neg M v i).trans hattain))
    rw [sum_update_eq, hwj] at h
    dsimp [w] at h
    rw [sum_update_eq] at h
    rw [hsum]
    convert h using 1
    congr 1
    dsimp [r]
    abel
  · intro hplus
    let z := ‖v i + v j‖⁻¹ • (v i + v j)
    have hz : ‖z‖ = 1 := by
      change ‖‖v i + v j‖⁻¹ • (v i + v j)‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hplus)]
    have hw : ∀ k, ‖pairUpdate v i j z z k‖ = 1 := by
      intro k
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [pairUpdate, hi, hj, hij, hz, hv]
    have h := hmax (pairUpdate v i j z z) hw
      (pair_average_attains M hM v hv hattain hij hplus)
    rw [sum_pairUpdate_eq v hij] at h
    rw [hsum]
    convert h using 1
    congr 1
    dsimp [r, z]
    rw [div_eq_mul_inv]
    module

end AltOMD.Polarization
