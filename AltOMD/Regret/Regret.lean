import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# From modified energy estimates to logarithmic regret

The sequence lemmas isolate the telescoping argument from the construction of the
modified energy. `scheduled_regret_bound` uses the sharpened constants and the
manuscript's horizon schedule. Its energy hypotheses are supplied by the analytic
modified-energy theorem, not additional axioms.
-/

namespace AltOMD

open Finset

lemma sum_increments (f : ℕ → ℝ) (T : ℕ) :
    ∑ k ∈ range T, (f (k + 1) - f k) = f T - f 0 := by
  induction T with
  | zero => simp
  | succ T ih => rw [sum_range_succ, ih]; ring

/-- The sum of both players' comparator regrets. -/
noncomputable def totalRegret {C : Type*} (cost : C → ℕ → ℝ) (T : ℕ) : ℝ :=
  sSup (Set.range fun c => ∑ k ∈ range T, cost c k)

theorem totalRegret_le {C : Type*} [Nonempty C] (cost : C → ℕ → ℝ) (T : ℕ)
    {B : ℝ} (h : ∀ c, ∑ k ∈ range T, cost c k ≤ B) : totalRegret cost T ≤ B := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact h c

/-- Telescoping the exact comparator identity. -/
theorem comparator_sum_identity {C : Type*} (cost : C → ℕ → ℝ)
    (H : ℕ → ℝ) (coupling : C → ℕ → ℝ) (η : ℝ) (T : ℕ)
    (hstep : ∀ c k, k < T → η * cost c k =
      H (k + 1) - H k + coupling c k - coupling c (k + 1)) (c : C) :
    η * (∑ k ∈ range T, cost c k) =
      H T - H 0 + coupling c 0 - coupling c T := by
  calc
    η * (∑ k ∈ range T, cost c k) =
        ∑ k ∈ range T, ((H (k + 1) - H k) -
          (coupling c (k + 1) - coupling c k)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      linarith [hstep c k (mem_range.mp hk)]
    _ = H T - H 0 + coupling c 0 - coupling c T := by
      rw [sum_sub_distrib, sum_increments, sum_increments]
      ring

/-- The energy difference controlled by closeness at the two endpoints and
per-step defects of the modified energy. -/
theorem energy_drift_bound (H modified : ℕ → ℝ) (T : ℕ) (δ ε : ℝ)
    (hzero : |H 0 - modified 0| ≤ δ) (hT : |H T - modified T| ≤ δ)
    (hstep : ∀ k < T, |modified (k + 1) - modified k| ≤ ε) :
    H T - H 0 ≤ 2 * δ + T * ε := by
  have hsum : modified T - modified 0 ≤ (T : ℝ) * ε := by
    rw [← sum_increments modified T]
    calc
      ∑ k ∈ range T, (modified (k + 1) - modified k) ≤ ∑ _k ∈ range T, ε := by
        apply sum_le_sum
        intro k hk
        exact (le_abs_self _).trans (hstep k (mem_range.mp hk))
      _ = (T : ℝ) * ε := by simp
  have hright := (le_abs_self (H T - modified T)).trans hT
  have hleft := (neg_le_abs (H 0 - modified 0)).trans hzero
  linarith

/-- The comparator estimate before substituting a horizon schedule. -/
theorem regret_from_energy {C : Type*} [Nonempty C]
    (cost : C → ℕ → ℝ) (H modified : ℕ → ℝ) (coupling : C → ℕ → ℝ)
    (T : ℕ) (η Λ δ ε : ℝ) (hη : 0 < η)
    (hstep : ∀ c k, k < T → η * cost c k =
      H (k + 1) - H k + coupling c k - coupling c (k + 1))
    (hterminal : ∀ c, 0 ≤ coupling c T) (hinitial : ∀ c, coupling c 0 ≤ Λ)
    (hzero : |H 0 - modified 0| ≤ δ) (hT : |H T - modified T| ≤ δ)
    (hdefect : ∀ k < T, |modified (k + 1) - modified k| ≤ ε) :
    totalRegret cost T ≤ (Λ + 2 * δ + T * ε) / η := by
  apply totalRegret_le
  intro c
  apply (le_div_iff₀ hη).2
  have hid := comparator_sum_identity cost H coupling η T hstep c
  have hdrift := energy_drift_bound H modified T δ ε hzero hT hdefect
  have hstart := hinitial c
  have hend := hterminal c
  nlinarith

/-- Exact constant-step horizon schedule, with the dyadic order as a natural logarithm. -/
noncomputable def stepSize (C₀ : ℝ) (T : ℕ) : ℝ :=
  1 / (16 * C₀ * ((Nat.log 2 T : ℝ) + 2))

lemma stepSize_pos {C₀ : ℝ} (hC : 0 < C₀) (T : ℕ) : 0 < stepSize C₀ T := by
  unfold stepSize
  positivity

lemma dyadic_horizon_bound (T : ℕ) :
    (T : ℝ) / (2 : ℝ) ^ (Nat.log 2 T + 1) ≤ 1 := by
  have hn := Nat.lt_pow_succ_log_self (b := 2) (by omega) T
  have hr : (T : ℝ) < (2 : ℝ) ^ (Nat.log 2 T + 1) := by exact_mod_cast hn
  apply (div_le_one (by positivity)).2
  exact hr.le

/-- Integer horizons satisfy the sharper bound needed by the quartic defect.
Indeed, `T ≤ 2^(N+1) - 1 ≤ 4^N` for `N = Nat.log 2 T`. -/
lemma quartic_horizon_bound (T : ℕ) :
    (T : ℝ) / (4 : ℝ) ^ (Nat.log 2 T + 1) ≤ (1 / 4 : ℝ) := by
  have hn := Nat.lt_pow_succ_log_self (b := 2) (by omega) T
  have hn' : T + 1 ≤ 2 ^ (Nat.log 2 T + 1) := by omega
  have hr : (T : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 T + 1) := by
    exact_mod_cast hn'
  have hpow : (4 : ℝ) ^ (Nat.log 2 T) =
      (2 : ℝ) ^ (Nat.log 2 T) * (2 : ℝ) ^ (Nat.log 2 T) := by
    rw [← mul_pow]
    norm_num
  have hquad : (T : ℝ) ≤ (4 : ℝ) ^ (Nat.log 2 T) := by
    rw [pow_succ] at hr
    rw [hpow]
    nlinarith [sq_nonneg ((2 : ℝ) ^ (Nat.log 2 T) - 1)]
  apply (div_le_iff₀ (by positivity)).2
  rw [pow_succ]
  nlinarith

/-- The numerical conclusion of the main theorem, for any sequence satisfying
the comparator identity and the two modified-energy estimates. -/
theorem scheduled_regret_bound_two_bounds {C : Type*} [Nonempty C]
    (cost : C → ℕ → ℝ) (H modified : ℕ → ℝ) (coupling : C → ℕ → ℝ)
    (T : ℕ) (C₀ Λ : ℝ) (hC : 0 < C₀) (hΛ : 0 ≤ Λ)
    (hstep : ∀ c k, k < T → stepSize C₀ T * cost c k =
      H (k + 1) - H k + coupling c k - coupling c (k + 1))
    (hterminal : ∀ c, 0 ≤ coupling c T) (hinitial : ∀ c, coupling c 0 ≤ Λ)
    (hzero : |H 0 - modified 0| ≤ (64 / 3 : ℝ) * C₀ ^ 2 * stepSize C₀ T)
    (hT : |H T - modified T| ≤ (64 / 3 : ℝ) * C₀ ^ 2 * stepSize C₀ T)
    (hdefect : ∀ k < T, |modified (k + 1) - modified k| ≤
      16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T / (4 : ℝ) ^ (Nat.log 2 T + 1)) :
    totalRegret cost T ≤ 16 * C₀ * Λ * ((Nat.log 2 T : ℝ) + 2) +
      ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ∧
      16 * C₀ * Λ * ((Nat.log 2 T : ℝ) + 2) +
      ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 ≤ 16 * C₀ * Λ * (Real.logb 2 T + 2) +
      ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
  have hη := stepSize_pos hC T
  have hraw := regret_from_energy cost H modified coupling T (stepSize C₀ T) Λ
    ((64 / 3 : ℝ) * C₀ ^ 2 * stepSize C₀ T)
    (16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T / (4 : ℝ) ^ (Nat.log 2 T + 1))
    hη hstep hterminal hinitial hzero hT hdefect
  have hquartic := quartic_horizon_bound T
  have hconst : 0 ≤ 16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T := by positivity
  have htail : (T : ℝ) *
      (16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T / (4 : ℝ) ^ (Nat.log 2 T + 1)) ≤
      4 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T := by
    calc
      _ = (16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T) *
          ((T : ℝ) / (4 : ℝ) ^ (Nat.log 2 T + 1)) := by ring
      _ ≤ (16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hquartic hconst
      _ = _ := by ring
  have hbound : totalRegret cost T ≤ Λ / stepSize C₀ T +
      ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
    apply hraw.trans
    apply (div_le_iff₀ hη).2
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hη)]
    nlinarith
  constructor
  · calc
      totalRegret cost T ≤ Λ / stepSize C₀ T +
          ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := hbound
      _ = 16 * C₀ * Λ * ((Nat.log 2 T : ℝ) + 2) +
          ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
        simp [stepSize, div_eq_mul_inv]
        ring
  · have hlog := Real.natLog_le_logb T 2
    gcongr
    exact_mod_cast hlog

/-- The real-logarithm consequence of the sharper two-bound theorem. -/
theorem scheduled_regret_bound {C : Type*} [Nonempty C]
    (cost : C → ℕ → ℝ) (H modified : ℕ → ℝ) (coupling : C → ℕ → ℝ)
    (T : ℕ) (C₀ Λ : ℝ) (hC : 0 < C₀) (hΛ : 0 ≤ Λ)
    (hstep : ∀ c k, k < T → stepSize C₀ T * cost c k =
      H (k + 1) - H k + coupling c k - coupling c (k + 1))
    (hterminal : ∀ c, 0 ≤ coupling c T) (hinitial : ∀ c, coupling c 0 ≤ Λ)
    (hzero : |H 0 - modified 0| ≤ (64 / 3 : ℝ) * C₀ ^ 2 * stepSize C₀ T)
    (hT : |H T - modified T| ≤ (64 / 3 : ℝ) * C₀ ^ 2 * stepSize C₀ T)
    (hdefect : ∀ k < T, |modified (k + 1) - modified k| ≤
      16 * Real.exp 2 * C₀ ^ 2 * stepSize C₀ T / (4 : ℝ) ^ (Nat.log 2 T + 1)) :
    totalRegret cost T ≤ 16 * C₀ * Λ * (Real.logb 2 T + 2) +
      ((128 / 3 : ℝ) + 4 * Real.exp 2) * C₀ ^ 2 := by
  have h := scheduled_regret_bound_two_bounds cost H modified coupling T C₀ Λ hC hΛ hstep hterminal hinitial hzero hT hdefect
  exact h.1.trans h.2

end AltOMD
