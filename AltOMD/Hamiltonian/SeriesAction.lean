import AltOMD.Hamiltonian.FormalEnergy
import AltOMD.Algebra.NoncommutativeSeries
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.PowerSeries.Exp
import Aesop

/-!
# Formal operator series acting on vector series

The Cauchy action respects multiplication of operator series.  Consequently,
coefficientwise exponentiation agrees with iterating the corresponding
positive-order operator on vector series.
-/

namespace AltOMD.SeriesAction

open scoped BigOperators

noncomputable section

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Cauchy action of a formal series of endomorphisms on a vector series. -/
def act (U : PowerSeries (Module.End R E)) (P : ℕ → E) (n : ℕ) : E :=
  ∑ ij ∈ Finset.antidiagonal n, PowerSeries.coeff ij.1 U (P ij.2)

theorem act_mul (U V : PowerSeries (Module.End R E)) (P : ℕ → E) :
    act (U * V) P = act U (act V P) := by
  funext n
  classical
  simp only [act, PowerSeries.coeff_mul, LinearMap.sum_apply,
    Module.End.mul_apply, map_sum, Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add simp [add_assoc])

@[simp] theorem act_one (P : ℕ → E) :
    act (1 : PowerSeries (Module.End R E)) P = P := by
  funext n
  simp [act, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [hk0]
  · simp

section Real

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

local instance : Algebra ℚ (Module.End ℝ E) :=
  Algebra.compHom (Module.End ℝ E) (algebraMap ℚ ℝ)

/-- The antidiagonal action is exactly the sequence action used by
`FormalEnergy`, with no conversion of the coefficients. -/
theorem act_eq_applySeries (U : PowerSeries (Module.End ℝ E)) (P : ℕ → E) :
    act U P = FormalEnergy.applySeries (fun n => PowerSeries.coeff n U) P := by
  funext n
  unfold act FormalEnergy.applySeries
  calc
    _ = ∑ ij ∈ Finset.antidiagonal n, PowerSeries.coeff ij.2 U (P ij.1) :=
      Finset.Nat.sum_antidiagonal_swap (n := n)
        (f := fun ij => PowerSeries.coeff ij.2 U (P ij.1))
    _ = _ := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff j U (P i)) n

theorem act_pow (U : PowerSeries (Module.End ℝ E)) (P : ℕ → E) (k : ℕ) :
    act (U ^ k) P = FormalEnergy.actionPower (act U) k P := by
  induction k with
  | zero => simp [FormalEnergy.actionPower]
  | succ k hk => rw [pow_succ', act_mul, hk]; rfl

/-- A positive-order operator series acts by shifting the action of its
positive coefficients.  This identifies a BCH logarithm with the generator
used in `FormalEnergy`. -/
theorem act_eq_shift_applySeries {U : PowerSeries (Module.End ℝ E)}
    (hU : U.constantCoeff = 0) (P : ℕ → E) :
    act U P = FormalEnergy.shift
      (FormalEnergy.applySeries (fun n => PowerSeries.coeff (n + 1) U) P) := by
  have h0 : PowerSeries.coeff 0 U = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hU
  rw [act_eq_applySeries]
  funext n
  cases n with
  | zero => simp [FormalEnergy.applySeries, FormalEnergy.shift, h0]
  | succ n =>
      change (∑ r ∈ Finset.range ((n + 1) + 1),
        PowerSeries.coeff (n + 1 - r) U (P r)) =
          ∑ r ∈ Finset.range (n + 1), PowerSeries.coeff (n - r + 1) U (P r)
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, h0, LinearMap.zero_apply, add_zero]
      apply Finset.sum_congr rfl
      intro r hr
      have hrn : r ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
      rw [show n + 1 - r = n - r + 1 by omega]

/-- Coefficientwise exponential, using real scalar coefficients.  Positive
order ensures that the finite coefficient sums equal the formal exponential. -/
def expSeries (U : PowerSeries (Module.End ℝ E)) :
    PowerSeries (Module.End ℝ E) :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1),
    (1 / (k.factorial : ℝ)) • PowerSeries.coeff n (U ^ k)

/-- The real-scalar coefficient formula agrees with scalar power-series
evaluation over the rationals. -/
theorem expSeries_eq_eval (U : PowerSeries (Module.End ℝ E)) :
    expSeries U = NoncommutativeSeries.eval U (PowerSeries.exp ℚ) := by
  apply PowerSeries.ext
  intro n
  rw [expSeries, PowerSeries.coeff_mk, NoncommutativeSeries.coeff_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [PowerSeries.coeff_exp, Algebra.algebraMap_self_apply]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    Rat.cast_smul_eq_qsmul ℝ (1 / (k.factorial : ℚ)) (PowerSeries.coeff n (U ^ k))

/-- Exponentiating an operator series and then acting is the same as
exponentiating its Cauchy action. -/
theorem act_expSeries {U : PowerSeries (Module.End ℝ E)}
    (hU : U.constantCoeff = 0) (P : ℕ → E) :
    act (expSeries U) P = FormalEnergy.expApply (act U) P := by
  funext n
  calc
    act (expSeries U) P n =
        ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n - r + 1),
          (1 / (k.factorial : ℝ)) • PowerSeries.coeff (n - r) (U ^ k) (P r) := by
      rw [act_eq_applySeries]
      simp [FormalEnergy.applySeries, expSeries, LinearMap.sum_apply]
    _ = ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (1 / (k.factorial : ℝ)) • PowerSeries.coeff (n - r) (U ^ k) (P r) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hkn
      have hnk : n - r < k := by simp only [Finset.mem_range] at hkn; omega
      simp [NoncommutativeSeries.coeff_pow_eq_zero hU hnk]
    _ = ∑ k ∈ Finset.range (n + 1),
          (1 / (k.factorial : ℝ)) • act (U ^ k) P n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [act_eq_applySeries]
      simp [FormalEnergy.applySeries, Finset.smul_sum]
    _ = FormalEnergy.expApply (act U) P n := by
      simp only [FormalEnergy.expApply, act_pow]

theorem act_eval_exp {U : PowerSeries (Module.End ℝ E)}
    (hU : U.constantCoeff = 0) (P : ℕ → E) :
    act (NoncommutativeSeries.eval U (PowerSeries.exp ℚ)) P =
      FormalEnergy.expApply (act U) P := by
  rw [← expSeries_eq_eval]
  exact act_expSeries hU P

end Real

end

end AltOMD.SeriesAction
