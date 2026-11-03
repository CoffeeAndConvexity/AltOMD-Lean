import AltOMD.Hamiltonian.Poisson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Derivative bound for one Poisson-bracket step

The derivative convolution from `Poisson.lean` supplies the induction step
used for Hamiltonian correction bounds in `HamiltonianBounds.lean`.
-/

noncomputable section

open scoped ContDiff

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The factorial cancellation behind the nested-bracket estimate. -/
theorem choose_mul_factorial_le (n s l : ℕ) (hl : l ≤ s) :
    s.choose l * (l + 1).factorial * (n + s - l + 1).factorial ≤
      (l + 1) * (n + s + 1).factorial := by
  have hmon : s.choose l ≤ (n + s + 1).choose l :=
    Nat.choose_le_choose l (by omega)
  have hfac := Nat.choose_mul_factorial_mul_factorial
    (n := n + s + 1) (k := l) (by omega)
  have hsub : n + s - l + 1 = n + s + 1 - l := by omega
  calc
    s.choose l * (l + 1).factorial * (n + s - l + 1).factorial ≤
        (n + s + 1).choose l * (l + 1).factorial *
          (n + s - l + 1).factorial := by gcongr
    _ = (l + 1) * ((n + s + 1).choose l * l.factorial *
        (n + s + 1 - l).factorial) := by rw [Nat.factorial_succ, hsub]; ring
    _ = (l + 1) * (n + s + 1).factorial := by rw [hfac]

/-- A finite geometric derivative sum; no infinite-series convergence is needed. -/
theorem sum_succ_div_two_pow_le (s : ℕ) :
    (∑ l ∈ Finset.range (s + 1), (l + 1 : ℝ) / 2 ^ l) ≤ 4 := by
  have hsum : ∀ s : ℕ,
      (∑ l ∈ Finset.range (s + 1), (l + 1 : ℝ) / 2 ^ l) =
        4 - (s + 3 : ℝ) / 2 ^ s := by
    intro s
    induction s with
    | zero => norm_num
    | succ s ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [pow_succ]
      field_simp
      ring
  rw [hsum]
  have : 0 ≤ (s + 3 : ℝ) / 2 ^ s := by positivity
  linarith

private theorem bracket_power_split (K : ℝ) (s l : ℕ) (hl : l ≤ s) :
    K ^ (l + 1) * (2 * K) ^ (s - l + 1) =
      (2 * K ^ 2) * (2 * K) ^ s / 2 ^ l := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hl
  simp only [Nat.add_sub_cancel_left, pow_add, pow_succ, mul_pow]
  field_simp

/-- One induction step, with the sum over derivative allocations evaluated explicitly. -/
theorem norm_iteratedFDeriv_poissonBracket_step_le
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (n s : ℕ) (x : E)
    (hf_bound : ∀ r, 1 ≤ r →
      ‖iteratedFDeriv ℝ r f x‖ ≤ K ^ r * r.factorial)
    (hg_bound : ∀ r, 1 ≤ r →
      ‖iteratedFDeriv ℝ r g x‖ ≤ C ^ n * (2 * K) ^ r * (n + r).factorial) :
    ‖iteratedFDeriv ℝ s (poissonBracket J f g) x‖ ≤
      (8 * ‖J‖ * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial := by
  apply (norm_iteratedFDeriv_poissonBracket_le J hf hg s x).trans
  have hterm : ∀ l ∈ Finset.range (s + 1),
      (s.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ *
        ‖iteratedFDeriv ℝ (s - l + 1) g x‖ ≤
      (2 * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial *
        ((l + 1 : ℝ) / 2 ^ l) := by
    intro l hl
    have hls : l ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hcomb : (s.choose l : ℝ) * (l + 1).factorial *
        (n + s - l + 1).factorial ≤ (l + 1 : ℝ) * (n + s + 1).factorial := by
      exact_mod_cast choose_mul_factorial_le n s l hls
    have hidx : n + (s - l + 1) = n + s - l + 1 := by omega
    calc
      (s.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ *
          ‖iteratedFDeriv ℝ (s - l + 1) g x‖ ≤
          (s.choose l : ℝ) * (K ^ (l + 1) * (l + 1).factorial) *
            (C ^ n * (2 * K) ^ (s - l + 1) * (n + (s - l + 1)).factorial) := by
              gcongr
              · exact hf_bound _ (by omega)
              · exact hg_bound _ (by omega)
      _ = C ^ n * (K ^ (l + 1) * (2 * K) ^ (s - l + 1)) *
          ((s.choose l : ℝ) * (l + 1).factorial * (n + s - l + 1).factorial) := by
            rw [hidx]
            ring
      _ ≤ C ^ n * (K ^ (l + 1) * (2 * K) ^ (s - l + 1)) *
          ((l + 1 : ℝ) * (n + s + 1).factorial) := by gcongr
      _ = (2 * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial *
          ((l + 1 : ℝ) / 2 ^ l) := by
            rw [bracket_power_split K s l hls]
            ring
  calc
    ‖J‖ * ∑ l ∈ Finset.range (s + 1),
        (s.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ *
          ‖iteratedFDeriv ℝ (s - l + 1) g x‖ ≤
        ‖J‖ * ∑ l ∈ Finset.range (s + 1),
          ((2 * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial *
            ((l + 1 : ℝ) / 2 ^ l)) := by
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (norm_nonneg J)
    _ = ‖J‖ * ((2 * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial) *
        (∑ l ∈ Finset.range (s + 1), (l + 1 : ℝ) / 2 ^ l) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤ ‖J‖ * ((2 * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial) * 4 := by
          gcongr
          exact sum_succ_div_two_pow_le s
    _ = (8 * ‖J‖ * K ^ 2) * C ^ n * (2 * K) ^ s * (n + s + 1).factorial := by ring

/-- The constant used by the manuscript. -/
def bracketConstant (J : (E →L[ℝ] ℝ) →L[ℝ] E) (K : ℝ) : ℝ :=
  24 * max ‖J‖ 1 * K ^ 2

end AltOMD
