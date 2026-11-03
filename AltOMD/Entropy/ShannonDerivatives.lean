import AltOMD.Entropy.Shannon.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Uniform derivatives of the Shannon conjugate

The local exponential sum is normalized to equal one at its expansion point.
Its multilinear coefficients have norm at most one, as do those of the
logarithm at one. The composition formula and the number of compositions
provide a dimension-independent coefficient bound. Symmetrization then bounds
the actual iterated Fréchet derivatives, without a convergence assumption on
the unrelated modified-Hamiltonian series.
-/

open scoped BigOperators ContDiff Topology
open Finset

namespace AltOMD.Shannon

noncomputable section

private theorem norm_iteratedFDeriv_le_series
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ} {x : E}
    (h : HasFPowerSeriesAt f p x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
  obtain ⟨r, h⟩ := h
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖iteratedFDeriv ℝ n f x v‖ =
        ‖∑ σ : Equiv.Perm (Fin n), p n (fun i => v (σ i))‖ :=
      congrArg norm (h.iteratedFDeriv_eq_sum_of_completeSpace v)
    _ ≤
        ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v (σ i)‖ := by
      exact sum_le_sum fun σ _ => (p n).le_opNorm _
    _ = ((n.factorial : ℝ) * ‖p n‖) * ∏ i, ‖v i‖ := by
      calc
        _ = ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
          apply sum_congr rfl
          intro σ _
          exact congrArg (fun a : ℝ => ‖p n‖ * a)
            (Equiv.prod_comp σ (fun i => ‖v i‖))
        _ = _ := by simp [Fintype.card_perm, mul_assoc]

private theorem norm_comp_series_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : FormalMultilinearSeries ℝ E ℝ) (q : FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ n, ‖p n‖ ≤ 1) (hq : ∀ n, ‖q n‖ ≤ 1) (n : ℕ) :
    ‖q.comp p n‖ ≤ (2 : ℝ) ^ (n - 1) := by
  calc
    ‖q.comp p n‖ ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Composition n, (1 : ℝ) := by
      apply sum_le_sum
      intro c _
      apply (q.compAlongComposition_norm p c).trans
      have hprod : (∏ i, ‖p (c.blocksFun i)‖) ≤ 1 :=
        prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hp _)
      exact mul_le_one₀ (hq _) (by positivity) hprod
    _ = (2 : ℝ) ^ (n - 1) := by simp [composition_card]

private def logSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  .ofScalars ℝ (fun n => -(-1 : ℝ) ^ n / n)

private theorem norm_logSeries_le (n : ℕ) : ‖logSeries n‖ ≤ 1 := by
  rw [logSeries, FormalMultilinearSeries.ofScalars_norm]
  cases n with
  | zero => simp
  | succ n =>
    simp only [norm_div, norm_neg, norm_pow, norm_one, one_pow, Real.norm_natCast]
    exact (div_le_one (by positivity)).2
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

variable {ι : Type*} [Fintype ι]

private def coord (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : ι => ℝ) i

private theorem norm_coord_le (i : ι) : ‖coord i‖ ≤ 1 := by
  refine (coord i).opNorm_le_bound zero_le_one ?_
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using (PiLp.norm_apply_le x i)

private def expCoordSeries (i : ι) :
    FormalMultilinearSeries ℝ (EuclideanSpace ℝ ι) ℝ :=
  (NormedSpace.expSeries ℝ ℝ).compContinuousLinearMap (coord i)

private theorem norm_expCoordSeries_le (i : ι) (n : ℕ) :
    ‖expCoordSeries i n‖ ≤ 1 := by
  apply ((NormedSpace.expSeries ℝ ℝ).norm_compContinuousLinearMap_le (coord i) n).trans
  have hpow : ‖coord i‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_coord_le i)
  have hexp : ‖NormedSpace.expSeries ℝ ℝ n‖ ≤ 1 := by
    rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm]
    simp only [norm_inv, Real.norm_natCast]
    exact inv_le_one_of_one_le₀
      (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n))
  exact mul_le_one₀ hexp (by positivity) hpow

private theorem expSum_pos_for_derivatives [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    0 < ∑ i, Real.exp (u i) :=
  sum_pos (fun i _ => Real.exp_pos (u i)) univ_nonempty

/-- The Shannon conjugate is smooth at every dual point. -/
theorem contDiff_logSumExp [Nonempty ι] :
    ContDiff ℝ ∞ (logSumExp : EuclideanSpace ℝ ι → ℝ) := by
  apply ContDiff.log
  · exact ContDiff.sum fun i _ => (coord i).contDiff.exp
  · intro u
    exact ne_of_gt (expSum_pos_for_derivatives u)

private theorem weight_nonneg [Nonempty ι] (u : EuclideanSpace ℝ ι) (i : ι) :
    0 ≤ softmax u i :=
  div_nonneg (Real.exp_pos _).le (expSum_pos_for_derivatives u).le

private theorem weights_sum [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    ∑ i, softmax u i = 1 := by
  simp only [softmax_apply, ← sum_div]
  exact div_self (ne_of_gt (expSum_pos_for_derivatives u))

private def normalizedExpSum (u v : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, softmax u i * Real.exp (v i - u i)

private def normalizedExpSeries (u : EuclideanSpace ℝ ι) :
    FormalMultilinearSeries ℝ (EuclideanSpace ℝ ι) ℝ :=
  ∑ i, softmax u i • expCoordSeries i

private theorem normalizedExpSum_self [Nonempty ι] (u : EuclideanSpace ℝ ι) :
    normalizedExpSum u u = 1 := by
  simpa [normalizedExpSum] using weights_sum u

private theorem norm_normalizedExpSeries_le [Nonempty ι]
    (u : EuclideanSpace ℝ ι) (n : ℕ) : ‖normalizedExpSeries u n‖ ≤ 1 := by
  classical
  let ev : FormalMultilinearSeries ℝ (EuclideanSpace ℝ ι) ℝ →+
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℝ :=
    { toFun := fun p => p n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have heval : normalizedExpSeries u n =
      ∑ i, softmax u i • expCoordSeries i n :=
    map_sum ev (fun i => softmax u i • expCoordSeries i) univ
  rw [heval]
  calc
    ‖∑ i, softmax u i • expCoordSeries i n‖ ≤
        ∑ i, ‖softmax u i • expCoordSeries i n‖ := norm_sum_le _ _
    _ ≤ ∑ i, softmax u i := by
      apply sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg u i)]
      exact mul_le_of_le_one_right (weight_nonneg u i) (norm_expCoordSeries_le i n)
    _ = 1 := weights_sum u

private theorem hasFPowerSeriesAt_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*} (s : Finset κ) (f : κ → E → ℝ)
    (p : κ → FormalMultilinearSeries ℝ E ℝ) (x : E)
    (h : ∀ i ∈ s, HasFPowerSeriesAt (f i) (p i) x) :
    HasFPowerSeriesAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, p i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasFPowerSeriesAt_const (𝕜 := ℝ) (c := (0 : ℝ)) (e := x))
  | @insert i s hi ih =>
    have hs := ih (fun j hj => h j (mem_insert_of_mem hj))
    simpa only [sum_insert hi, Pi.add_def] using (h i (mem_insert_self _ _)).add hs

private theorem hasFPowerSeriesAt_expCoord (u : EuclideanSpace ℝ ι) (i : ι) :
    HasFPowerSeriesAt (fun v : EuclideanSpace ℝ ι => Real.exp (v i - u i))
      (expCoordSeries i) u := by
  have hexp : HasFPowerSeriesAt Real.exp (NormedSpace.expSeries ℝ ℝ) 0 := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_hasFPowerSeriesAt_zero
  have hcoord : HasFPowerSeriesAt (Real.exp ∘ coord i) (expCoordSeries i) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using hexp
  simpa [coord, Function.comp_def] using hcoord.comp_sub u

private theorem hasFPowerSeriesAt_normalizedExpSum (u : EuclideanSpace ℝ ι) :
    HasFPowerSeriesAt (normalizedExpSum u) (normalizedExpSeries u) u := by
  classical
  apply hasFPowerSeriesAt_finset_sum
  intro i _
  simpa only [Pi.smul_def, smul_eq_mul] using
    (hasFPowerSeriesAt_expCoord u i).const_smul (c := softmax u i)

private theorem normalizedExpSum_eq_div [Nonempty ι] (u v : EuclideanSpace ℝ ι) :
    normalizedExpSum u v = (∑ i, Real.exp (v i)) / ∑ i, Real.exp (u i) := by
  rw [normalizedExpSum, sum_div]
  apply sum_congr rfl
  intro i _
  rw [softmax_apply, Real.exp_sub]
  field_simp [ne_of_gt (expSum_pos_for_derivatives u), Real.exp_ne_zero]

private theorem log_normalizedExpSum [Nonempty ι] (u v : EuclideanSpace ℝ ι) :
    Real.log (normalizedExpSum u v) = logSumExp v - logSumExp u := by
  rw [normalizedExpSum_eq_div, Real.log_div
    (ne_of_gt (expSum_pos_for_derivatives v)) (ne_of_gt (expSum_pos_for_derivatives u))]
  rfl

/-- A dimension-independent bound on the full multilinear norm of every
positive-order derivative of the Shannon conjugate. -/
theorem norm_iteratedFDeriv_logSumExp_le_sharp [Nonempty ι]
    (n : ℕ) (u : EuclideanSpace ℝ ι) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n logSumExp u‖ ≤ (2 : ℝ) ^ (n - 1) * n.factorial := by
  have hlog : HasFPowerSeriesAt Real.log logSeries (normalizedExpSum u u) := by
    rw [normalizedExpSum_self]
    exact hasFPowerSeriesAt_log_one
  have hseries := hlog.comp (hasFPowerSeriesAt_normalizedExpSum u)
  have hbound := norm_iteratedFDeriv_le_series hseries n
  have hcoeff := norm_comp_series_le (normalizedExpSeries u) logSeries
    (norm_normalizedExpSeries_le u) norm_logSeries_le n
  have heq : Real.log ∘ normalizedExpSum u = fun v => logSumExp v - logSumExp u := by
    funext v
    exact log_normalizedExpSum u v
  have hderiv : iteratedFDeriv ℝ n (Real.log ∘ normalizedExpSum u) u =
      iteratedFDeriv ℝ n logSumExp u := by
    rw [heq]
    change iteratedFDeriv ℝ n
      (logSumExp - fun _ : EuclideanSpace ℝ ι => logSumExp u) u = _
    rw [iteratedFDeriv_sub
      (contDiff_logSumExp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
      contDiff_const]
    simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (n := n) (by omega)]
  rw [hderiv] at hbound
  calc
    ‖iteratedFDeriv ℝ n logSumExp u‖ ≤ (n.factorial : ℝ) * ‖logSeries.comp (normalizedExpSeries u) n‖ := hbound
    _ ≤ (n.factorial : ℝ) * (2 : ℝ) ^ (n - 1) := mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = (2 : ℝ) ^ (n - 1) * n.factorial := mul_comm _ _

/-- The pointwise derivative bound in `prop:shannon`, with the manuscript's
constant, follows from the stronger full multilinear estimate. -/
theorem norm_iteratedFDeriv_logSumExp_le_manuscript [Nonempty ι]
    (n : ℕ) (u : EuclideanSpace ℝ ι) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n logSumExp u‖ ≤ (1 / 2 : ℝ) * 4 ^ n * n.factorial := by
  apply (norm_iteratedFDeriv_logSumExp_le_sharp n u hn).trans
  have hp : (2 : ℝ) * 2 ^ (n - 1) ≤ 4 ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n.factorial :
    (0 : ℝ) ≤ n.factorial)]

/-- The literal uniform derivative estimate `eq:shannon-derivative-bound`:
the supremum ranges over the entire Euclidean dual space. -/
theorem sup_norm_iteratedFDeriv_logSumExp_le_manuscript [Nonempty ι]
    (n : ℕ) (hn : 1 ≤ n) :
    (⨆ u : EuclideanSpace ℝ ι, ‖iteratedFDeriv ℝ n logSumExp u‖) ≤
      (1 / 2 : ℝ) * 4 ^ n * n.factorial :=
  ciSup_le fun u => norm_iteratedFDeriv_logSumExp_le_manuscript n u hn

/-- The earlier, looser factorial bound, retained as a consequence of the
stronger full multilinear estimate. -/
theorem norm_iteratedFDeriv_logSumExp_le [Nonempty ι]
    (n : ℕ) (u : EuclideanSpace ℝ ι) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n logSumExp u‖ ≤ (16 : ℝ) ^ n * n.factorial := by
  apply (norm_iteratedFDeriv_logSumExp_le_sharp n u hn).trans
  have hp : (2 : ℝ) ^ (n - 1) ≤ (16 : ℝ) ^ n :=
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
  exact mul_le_mul_of_nonneg_right hp (by positivity)

end

end AltOMD.Shannon
