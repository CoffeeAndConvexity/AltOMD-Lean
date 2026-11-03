import AltOMD.Hamiltonian.Poisson
import Mathlib.Data.EReal.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Scalar formal-series bounds for the actual derivatives of a Lie derivative. -/

noncomputable section
open scoped ContDiff
open Finset

namespace AltOMD.ScalarMajorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The global derivative norm. The theorems below record boundedness separately. -/
def derivativeSup (f : E → ℝ) (s : ℕ) : ℝ :=
  sSup (Set.range fun x => ‖iteratedFDeriv ℝ s f x‖)

/-- The global derivative norm in the extended reals, without a finiteness premise. -/
def extendedDerivativeSup (f : E → ℝ) (s : ℕ) : EReal :=
  ⨆ x, (‖iteratedFDeriv ℝ s f x‖ : EReal)

theorem norm_derivative_le_of_extended (f : E → ℝ) (s : ℕ) (M : ℝ)
    (h : extendedDerivativeSup f s ≤ (M : EReal)) (x : E) :
    ‖iteratedFDeriv ℝ s f x‖ ≤ M :=
  EReal.coe_le_coe_iff.mp ((le_iSup (fun y =>
    (‖iteratedFDeriv ℝ s f y‖ : EReal)) x).trans h)

theorem derivative_sum_le_of_extended (f g : E → ℝ) (s : ℕ) (M : ℝ)
    (h : extendedDerivativeSup f s + extendedDerivativeSup g s ≤ (M : EReal))
    (x y : E) :
    ‖iteratedFDeriv ℝ s f x‖ + ‖iteratedFDeriv ℝ s g y‖ ≤ M := by
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_add]
  exact (add_le_add (le_iSup (fun z => (‖iteratedFDeriv ℝ s f z‖ : EReal)) x)
    (le_iSup (fun z => (‖iteratedFDeriv ℝ s g z‖ : EReal)) y)).trans h

theorem derivativeSup_le (f : E → ℝ) (s : ℕ) (M : ℝ)
    (h : ∀ x, ‖iteratedFDeriv ℝ s f x‖ ≤ M) : derivativeSup f s ≤ M :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact h x)

theorem norm_derivative_le_sup (f : E → ℝ) (s : ℕ)
    (h : BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s f x‖)) (x : E) :
    ‖iteratedFDeriv ℝ s f x‖ ≤ derivativeSup f s :=
  le_csSup h (Set.mem_range_self x)

/-- The formal series `(1 - K X)⁻²`. -/
def inverseSquare (K : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale K (PowerSeries.invOneSubPow ℝ 2).val

@[simp] theorem coeff_inverseSquare (K : ℝ) (s : ℕ) :
    PowerSeries.coeff s (inverseSquare K) = (s + 1) * K ^ s := by
  simp [inverseSquare, PowerSeries.invOneSubPow, PowerSeries.coeff_mk,
    Nat.choose_one_right, mul_comm, Nat.cast_add, Nat.cast_one, add_comm]

theorem inverseSquare_mul (K : ℝ) :
    inverseSquare K * (1 - PowerSeries.C K * PowerSeries.X) ^ 2 = 1 := by
  have h := congrArg (PowerSeries.rescale K)
    (PowerSeries.invOneSubPow ℝ 2).val_inv
  simpa only [map_mul, map_pow, map_sub, map_one,
    PowerSeries.invOneSubPow_inv_eq_one_sub_pow, PowerSeries.rescale_X,
    inverseSquare] using h

theorem inverseSquare_eq (K : ℝ) :
    inverseSquare K = ((1 - PowerSeries.C K * PowerSeries.X) ^ 2)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
  exact inverseSquare_mul K

/-- The manuscript's scalar vector-field majorant `‖J‖ K (1 - K X)⁻²`. -/
def vectorMajorant (J : (E →L[ℝ] ℝ) →L[ℝ] E) (K : ℝ) : PowerSeries ℝ :=
  PowerSeries.C (‖J‖ * K) * inverseSquare K

@[simp] theorem coeff_vectorMajorant (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (K : ℝ) (s : ℕ) :
    PowerSeries.coeff s (vectorMajorant J K) = ‖J‖ * K * (s + 1) * K ^ s := by
  simp only [vectorMajorant, PowerSeries.coeff_C_mul, coeff_inverseSquare]
  ring

theorem vectorMajorant_eq (J : (E →L[ℝ] ℝ) →L[ℝ] E) (K : ℝ) :
    vectorMajorant J K = PowerSeries.C (‖J‖ * K) *
      ((1 - PowerSeries.C K * PowerSeries.X) ^ 2)⁻¹ := by
  rw [vectorMajorant, inverseSquare_eq]

private theorem choose_factorials (s l : ℕ) (hl : l ≤ s) :
    (s.choose l : ℝ) * ((l + 1).factorial : ℝ) * ((s - l + 1).factorial : ℝ) =
      (s.factorial : ℝ) * (l + 1) * (((s - l : ℕ) : ℝ) + 1) := by
  have h : (s.choose l : ℝ) * (l.factorial : ℝ) * ((s - l).factorial : ℝ) =
      (s.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  calc
    (s.choose l : ℝ) * ((l + 1) * l.factorial) * ((((s - l : ℕ) : ℝ) + 1) * (s - l).factorial) =
        ((s.choose l : ℝ) * l.factorial * (s - l).factorial) * (l + 1) * (((s - l : ℕ) : ℝ) + 1) := by ring
    _ = _ := by rw [h]

/-- The coefficient of the product with the formal derivative, as a finite sum. -/
theorem coeff_product (J : (E →L[ℝ] ℝ) →L[ℝ] E) (K : ℝ)
    (b : PowerSeries ℝ) (s : ℕ) :
    PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) =
      ∑ l ∈ range (s + 1),
        (PowerSeries.coeff (l + 1) b * (l + 1)) *
          (‖J‖ * K * (((s - l : ℕ) : ℝ) + 1) * K ^ (s - l)) := by
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_derivative, coeff_vectorMajorant, Nat.cast_add,
    Nat.cast_one]

/-- A coefficientwise scalar majorant bounds every derivative at every point. -/
theorem lie_derivative_pointwise
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) {f Q : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hQ : ContDiff ℝ ∞ Q)
    {K : ℝ} (hK : 0 ≤ K) (b : PowerSeries ℝ)
    (hb : ∀ s, 0 ≤ PowerSeries.coeff s b)
    (hQbound : ∀ r x, 1 ≤ r →
      ‖iteratedFDeriv ℝ r Q x‖ ≤ K ^ r * r.factorial)
    (hfbound : ∀ r x, 1 ≤ r →
      ‖iteratedFDeriv ℝ r f x‖ / r.factorial ≤ PowerSeries.coeff r b)
    (s : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ s (poissonBracket J f Q) x‖ / s.factorial ≤
      PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) := by
  have hfac : (0 : ℝ) < s.factorial := by positivity
  apply (div_le_iff₀ hfac).2
  rw [coeff_product, Finset.sum_mul]
  have hprod := norm_iteratedFDeriv_poissonBracket_le J hf hQ s x
  apply hprod.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hls : l ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hf' : ‖iteratedFDeriv ℝ (l + 1) f x‖ ≤
      PowerSeries.coeff (l + 1) b * ((l + 1).factorial : ℝ) :=
    (div_le_iff₀ (by positivity)).mp (hfbound (l + 1) x (by omega))
  have hQ' := hQbound (s - l + 1) x (by omega)
  calc
    ‖J‖ * ((s.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) f x‖ *
        ‖iteratedFDeriv ℝ (s - l + 1) Q x‖) ≤
      ‖J‖ * ((s.choose l : ℝ) *
        (PowerSeries.coeff (l + 1) b * (l + 1).factorial) *
          (K ^ (s - l + 1) * (s - l + 1).factorial)) := by
      gcongr
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hb _) (Nat.cast_nonneg _))
    _ = ((s.choose l : ℝ) * (l + 1).factorial * (s - l + 1).factorial) *
        (‖J‖ * PowerSeries.coeff (l + 1) b * K ^ (s - l + 1)) := by ring
    _ = _ := by rw [choose_factorials s l hls, pow_succ]; ring

/-- The manuscript's scalar formal-majorant conclusion, including finiteness
of every output supremum. Input finiteness makes the real supremum faithful. -/
theorem lie_derivative_majorant
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) {f Q : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hQ : ContDiff ℝ ∞ Q)
    {K : ℝ} (hK : 0 ≤ K) (b : PowerSeries ℝ)
    (hb : ∀ s, 0 ≤ PowerSeries.coeff s b)
    (hQbound : ∀ r x, 1 ≤ r →
      ‖iteratedFDeriv ℝ r Q x‖ ≤ K ^ r * r.factorial)
    (hfbdd : ∀ r, 1 ≤ r → BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ r f x‖))
    (hfbound : ∀ r, 1 ≤ r → derivativeSup f r / r.factorial ≤ PowerSeries.coeff r b)
    (s : ℕ) :
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (poissonBracket J f Q) x‖) ∧
      derivativeSup (poissonBracket J f Q) s / s.factorial ≤
        PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) := by
  have hpoint (x : E) := lie_derivative_pointwise J hf hQ hK b hb hQbound
    (fun r x hr => (div_le_div_of_nonneg_right
      (norm_derivative_le_sup f r (hfbdd r hr) x) (by positivity)).trans (hfbound r hr)) s x
  have hbound (x : E) : ‖iteratedFDeriv ℝ s (poissonBracket J f Q) x‖ ≤
      PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) * s.factorial :=
    (div_le_iff₀ (by positivity)).mp (hpoint x)
  refine ⟨⟨PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) *
    (s.factorial : ℝ), ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbound x
  · exact (div_le_iff₀ (by positivity)).2
      (derivativeSup_le _ s _ hbound)

/-- The source lemma for either Hamiltonian under the summed standing
regularity assumption. The selected Hamiltonian bound is derived internally. -/
theorem lie_derivative_majorant_source
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (F G f : E → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hf : ContDiff ℝ ∞ f)
    {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ r, 1 ≤ r → ∀ x y,
      ‖iteratedFDeriv ℝ r F x‖ + ‖iteratedFDeriv ℝ r G y‖ ≤ K ^ r * r.factorial)
    (Q : E → ℝ) (hQchoice : Q = F ∨ Q = G) (b : PowerSeries ℝ)
    (hb : ∀ s, 0 ≤ PowerSeries.coeff s b)
    (hfbdd : ∀ r, 1 ≤ r → BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ r f x‖))
    (hfbound : ∀ r, 1 ≤ r → derivativeSup f r / r.factorial ≤ PowerSeries.coeff r b)
    (s : ℕ) :
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (poissonBracket J f Q) x‖) ∧
      derivativeSup (poissonBracket J f Q) s / s.factorial ≤
        PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) := by
  rcases hQchoice with rfl | rfl
  · apply lie_derivative_majorant J hf hF (le_trans zero_le_one hK) b hb
      ?_ hfbdd hfbound s
    intro r x hr
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hregularity r hr x 0)
  · apply lie_derivative_majorant J hf hG (le_trans zero_le_one hK) b hb
      ?_ hfbdd hfbound s
    intro r y hr
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hregularity r hr 0 y)

/-- The source assumptions as extended global suprema. Finite coefficient
bounds supply every required real-supremum boundedness proof internally. -/
theorem lie_derivative_majorant_source_ereal
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (F G f : E → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hf : ContDiff ℝ ∞ f)
    {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ r, 1 ≤ r →
      extendedDerivativeSup F r + extendedDerivativeSup G r ≤
        ((K ^ r * r.factorial : ℝ) : EReal))
    (Q : E → ℝ) (hQchoice : Q = F ∨ Q = G) (b : PowerSeries ℝ)
    (hb : ∀ s, 0 ≤ PowerSeries.coeff s b)
    (hfbound : ∀ r, 1 ≤ r → extendedDerivativeSup f r ≤
      ((PowerSeries.coeff r b * r.factorial : ℝ) : EReal))
    (s : ℕ) :
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (poissonBracket J f Q) x‖) ∧
      derivativeSup (poissonBracket J f Q) s / s.factorial ≤
        PowerSeries.coeff s (vectorMajorant J K * PowerSeries.derivative ℝ b) := by
  have hpoint (r : ℕ) (hr : 1 ≤ r) (x : E) :
      ‖iteratedFDeriv ℝ r f x‖ ≤ PowerSeries.coeff r b * r.factorial :=
    norm_derivative_le_of_extended f r _ (hfbound r hr) x
  apply lie_derivative_majorant_source J F G f hF hG hf hK
    (fun r hr x y => derivative_sum_le_of_extended F G r _ (hregularity r hr) x y)
    Q hQchoice b hb
  · intro r hr
    exact ⟨PowerSeries.coeff r b * (r.factorial : ℝ),
      by rintro _ ⟨x, rfl⟩; exact hpoint r hr x⟩
  · intro r hr
    exact (div_le_iff₀ (by positivity)).2 (derivativeSup_le f r _ (hpoint r hr))

end AltOMD.ScalarMajorant
