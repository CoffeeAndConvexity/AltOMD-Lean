import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-! # Real polarization for symmetric continuous multilinear maps -/

open Finset Function
open scoped BigOperators

namespace AltOMD.Polarization

private def sign (b : Bool) : ℝ := if b then -1 else 1

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
private theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
private theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

private def flip {n : ℕ} (k : Fin n) (ε : Fin n → Bool) : Fin n → Bool :=
  Function.update ε k (!(ε k))

private theorem flip_flip {n : ℕ} (k : Fin n) (ε : Fin n → Bool) :
    flip k (flip k ε) = ε := by
  funext i
  by_cases h : i = k <;> simp [flip, h]

private theorem prod_sign_flip {n : ℕ} (k : Fin n) (ε : Fin n → Bool) :
    (∏ i, sign (flip k ε i)) = -(∏ i, sign (ε i)) := by
  have h : (fun i => sign (flip k ε i)) =
      Function.update (fun i => sign (ε i)) k (-sign (ε k)) := by
    funext i
    by_cases hi : i = k <;> simp [flip, hi, sign_not]
  rw [h, prod_update_of_mem (mem_univ k)]
  have hold := prod_update_of_mem (mem_univ k) (fun i => sign (ε i)) (sign (ε k))
  rw [Function.update_eq_self] at hold
  rw [hold]
  ring

private theorem sign_orthogonality {n : ℕ} (f : Fin n → Fin n) :
    (∑ ε : Fin n → Bool, (∏ i, sign (ε i)) * (∏ i, sign (ε (f i)))) =
      if Function.Bijective f then (2 : ℝ) ^ n else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [if_pos hf]
    have hprod (ε : Fin n → Bool) :
        (∏ i, sign (ε (f i))) = ∏ i, sign (ε i) :=
      (Equiv.ofBijective f hf).prod_comp (fun i => sign (ε i))
    simp_rw [hprod, ← prod_mul_distrib, sign_sq]
    simp
  · rw [if_neg hf]
    have hns : ¬ Function.Surjective f := fun hs => hf (Finite.surjective_iff_bijective.mp hs)
    obtain ⟨k, hk⟩ : ∃ k, ∀ i, f i ≠ k := by simpa [Function.Surjective] using hns
    let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
      ⟨flip k, flip k, flip_flip k, flip_flip k⟩
    have heq : (∑ ε : Fin n → Bool, (∏ i, sign (ε i)) * (∏ i, sign (ε (f i)))) =
        -(∑ ε : Fin n → Bool, (∏ i, sign (ε i)) * (∏ i, sign (ε (f i)))) := by
      calc
        _ = ∑ ε : Fin n → Bool,
            (∏ i, sign (flip k ε i)) * (∏ i, sign (flip k ε (f i))) :=
          (e.sum_comp _).symm
        _ = _ := by
          simp_rw [prod_sign_flip]
          simp only [flip, Function.update_of_ne (hk _), neg_mul,
            sum_neg_distrib]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The signed polarization identity. Symmetry means invariance under every
permutation of the argument positions. -/
theorem identity {n : ℕ} (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    (v : Fin n → E) :
    (2 : ℝ) ^ n * n.factorial * M v =
      ∑ ε : Fin n → Bool, (∏ i, sign (ε i)) *
        M (fun _ => ∑ i, sign (ε i) • v i) := by
  classical
  have hexpand (ε : Fin n → Bool) :
      M (fun _ => ∑ i, sign (ε i) • v i) =
        ∑ f : Fin n → Fin n, (∏ i, sign (ε (f i))) * M (v ∘ f) := by
    change M.toMultilinearMap (fun _ : Fin n => ∑ i, sign (ε i) • v i) = _
    rw [M.toMultilinearMap.map_sum]
    apply sum_congr rfl
    intro f _
    exact M.map_smul_univ _ _
  rw [show (∑ ε : Fin n → Bool, (∏ i, sign (ε i)) *
      M (fun _ => ∑ i, sign (ε i) • v i)) =
      ∑ f : Fin n → Fin n,
        (if Function.Bijective f then (2 : ℝ) ^ n else 0) * M (v ∘ f) from by
    simp_rw [hexpand, mul_sum, ← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul, sign_orthogonality]]
  symm
  calc
    _ = ∑ f : {f : Fin n → Fin n // Function.Bijective f},
        (2 : ℝ) ^ n * M (v ∘ f.val) := by
      simpa only [sum_filter, ite_mul, zero_mul] using
        (Finset.sum_subtype (univ.filter (fun f : Fin n → Fin n => Function.Bijective f))
          (by simp) (fun f => (2 : ℝ) ^ n * M (v ∘ f)))
    _ = ∑ σ : Equiv.Perm (Fin n), (2 : ℝ) ^ n * M (v ∘ σ) :=
      (Equiv.bijectiveEquiv.symm.sum_comp _).symm
    _ = _ := by simp [hM, Fintype.card_perm, mul_assoc, mul_comm, mul_left_comm]

private theorem diagonal_bound {n : ℕ} (hn : 0 < n)
    (M : E [×n]→L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h : E, ‖h‖ ≤ 1 → |M (fun _ => h)| ≤ C) (h : E) :
    |M (fun _ => h)| ≤ ‖h‖ ^ n * C := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_cases hh : h = 0
  · have hz : M (fun _ => (0 : E)) = 0 := M.map_coord_zero ⟨0, hn⟩ rfl
    simp [hh, hz, hn.ne']
  have hnz : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  have hunit : ‖‖h‖⁻¹ • h‖ ≤ 1 := by
    simp [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz]
  have heq : M (fun _ => h) = ‖h‖ ^ n * M (fun _ => ‖h‖⁻¹ • h) := by
    calc
      _ = M (fun _ => ‖h‖ • (‖h‖⁻¹ • h)) := by simp [smul_smul, hnz]
      _ = _ := by rw [M.map_smul_univ]; simp [smul_eq_mul]
  rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact mul_le_mul_of_nonneg_left (hb _ hunit) (by positivity)

private theorem unit_bound {n : ℕ} (hn : 0 < n) (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ h : E, ‖h‖ ≤ 1 → |M (fun _ => h)| ≤ C)
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
    |M v| ≤ ((n : ℝ) ^ n / n.factorial) * C := by
  have hdiag (ε : Fin n → Bool) :
      |M (fun _ => ∑ i, sign (ε i) • v i)| ≤ (n : ℝ) ^ n * C := by
    apply (diagonal_bound hn M hC hb _).trans
    have hs : ‖∑ i, sign (ε i) • v i‖ ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ i, ‖sign (ε i) • v i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply sum_le_sum
          intro i _
          simpa [norm_smul, Real.norm_eq_abs, abs_sign] using hv i
        _ = _ := by simp
    gcongr
  have hsum : (2 : ℝ) ^ n * n.factorial * |M v| ≤
      (2 : ℝ) ^ n * ((n : ℝ) ^ n * C) := by
    calc
      _ = |(2 : ℝ) ^ n * n.factorial * M v| := by
        simp [abs_mul, abs_of_nonneg, Nat.cast_nonneg]
      _ = |∑ ε : Fin n → Bool, (∏ i, sign (ε i)) *
          M (fun _ => ∑ i, sign (ε i) • v i)| := congrArg abs (identity M hM v)
      _ ≤ ∑ ε : Fin n → Bool, |(∏ i, sign (ε i)) *
          M (fun _ => ∑ i, sign (ε i) • v i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ε : Fin n → Bool, (n : ℝ) ^ n * C := by
        apply sum_le_sum
        intro ε _
        simpa [abs_mul, abs_prod, abs_sign] using hdiag ε
      _ = _ := by simp
  have hcancel : (n.factorial : ℝ) * |M v| ≤ (n : ℝ) ^ n * C :=
    (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using hsum)
  calc
    |M v| ≤ ((n : ℝ) ^ n * C) / n.factorial :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)).2
        (by simpa [mul_comm] using hcancel)
    _ = _ := by ring

/-- The real polarization bound, in its sharper `n^n/n!` form. -/
theorem norm_le_mul_diagonal_bound {n : ℕ} (hn : 0 < n) (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ h : E, ‖h‖ ≤ 1 → |M (fun _ => h)| ≤ C) :
    ‖M‖ ≤ ((n : ℝ) ^ n / n.factorial) * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let w : Fin n → E := fun i => ‖v i‖⁻¹ • v i
  have hw (i : Fin n) : ‖w i‖ ≤ 1 := by
    dsimp [w]
    by_cases hi : v i = 0
    · simp [hi]
    · simp [norm_smul, norm_inv, norm_norm, norm_ne_zero_iff.mpr hi]
  have heq : v = fun i => ‖v i‖ • w i := by
    funext i
    by_cases hi : v i = 0
    · simp [hi, w]
    · simp [w, smul_smul, norm_ne_zero_iff.mpr hi]
  calc
    ‖M v‖ = (∏ i, ‖v i‖) * |M w| := by
      conv_lhs => rw [heq]
      rw [M.map_smul_univ, norm_smul]
      simp [Real.norm_eq_abs, abs_prod, abs_of_nonneg (norm_nonneg _)]
    _ ≤ (∏ i, ‖v i‖) * (((n : ℝ) ^ n / n.factorial) * C) :=
      mul_le_mul_of_nonneg_left (unit_bound hn M hM hC hb w hw) (by positivity)
    _ = _ := by ring

/-- Symmetric multilinear maps on a real normed space are controlled by their
diagonal values with a dimension-independent exponential factor. -/
theorem norm_le_exp_mul_diagonal_bound {n : ℕ} (hn : 0 < n) (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ h : E, ‖h‖ ≤ 1 → |M (fun _ => h)| ≤ C) :
    ‖M‖ ≤ Real.exp n * C :=
  (norm_le_mul_diagonal_bound hn M hM hC hb).trans
    (mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp n (Nat.cast_nonneg n) n) hC)

private theorem diagonal_bddAbove {n : ℕ} (M : E [×n]→L[ℝ] ℝ) :
    BddAbove ((fun h : E => |M (fun _ => h)|) '' Metric.closedBall 0 1) := by
  refine ⟨‖M‖, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  have hh' : ‖h‖ ≤ 1 := by simpa using hh
  have hb := M.le_opNorm (fun _ => h)
  simp only [Real.norm_eq_abs, prod_const, card_univ, Fintype.card_fin] at hb
  exact hb.trans (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hh'))

/-- The supremum form of the general real-polarization estimate. For the
Hilbert-space equality in the appendix, see `norm_eq_diagonal_sup`. -/
theorem real_polarization {n : ℕ} (hn : 1 ≤ n) (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v) :
    ‖M‖ ≤ Real.exp n *
      sSup ((fun h : E => |M (fun _ => h)|) '' Metric.closedBall 0 1) := by
  apply norm_le_exp_mul_diagonal_bound hn M hM
  · exact (abs_nonneg _).trans (le_csSup (diagonal_bddAbove M) ⟨0, by simp, rfl⟩)
  · intro h hh
    exact le_csSup (diagonal_bddAbove M) ⟨h, by simpa using hh, rfl⟩

end AltOMD.Polarization
