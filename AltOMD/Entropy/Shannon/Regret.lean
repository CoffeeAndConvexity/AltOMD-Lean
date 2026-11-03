import AltOMD.Entropy.Shannon.Basic
import AltOMD.Entropy.Duality
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Shannon comparator radii and multiplicative weights

The Bregman identity includes boundary comparators under the convention
`0 * log 0 = 0`. The update identities use arbitrary real step sizes.
-/

open Set
open scoped BigOperators InnerProductSpace

namespace AltOMD.Shannon

variable {ι : Type*} [Fintype ι]

/-- The Kullback--Leibler expression, with zero summands at zero coordinates. -/
noncomputable def kl (c x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, c i * Real.log (c i / x i)

/-- An entropy Bregman divergence has its usual coordinate expression. -/
theorem bregman_entropyGradient_eq {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) :
    Duality.bregman entropy (entropyGradient x) c x =
      entropy c - ∑ i, c i * Real.log (x i) := by
  have hi : ⟪entropyGradient x, c - x⟫_ℝ =
      (∑ i, c i) - (∑ i, x i) + (∑ i, c i * Real.log (x i)) - entropy x := by
    simp only [PiLp.inner_apply, Real.inner_apply, entropyGradient_apply, PiLp.sub_apply, entropy]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Duality.bregman, hi, hc.2, hx.2]
  ring

/-- The coordinate expression is KL, including comparators on the boundary. -/
theorem bregman_entropyGradient_eq_kl {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    Duality.bregman entropy (entropyGradient x) c x = kl c x := by
  rw [bregman_entropyGradient_eq hc hx]
  unfold entropy kl
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hci : c i = 0
  · simp [hci]
  · rw [Real.log_div hci (ne_of_gt (hpos i))]
    ring

/-- Every probability coordinate is at most one. -/
theorem coordinate_le_one {x : EuclideanSpace ℝ ι} (hx : x ∈ simplex) (i : ι) :
    x i ≤ 1 := by
  classical
  rw [← hx.2]
  exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

/-- Negative Shannon entropy is nonpositive on the closed simplex. -/
theorem entropy_nonpos {c : EuclideanSpace ℝ ι} (hc : c ∈ simplex) : entropy c ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (hc.1 i)
    (Real.log_nonpos (hc.1 i) (coordinate_le_one hc i))

/-- Any positive lower bound on the initial coordinates bounds every comparator. -/
theorem bregman_entropyGradient_le_log_inv {c x : EuclideanSpace ℝ ι} {δ : ℝ}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hδ : 0 < δ) (hbound : ∀ i, δ ≤ x i) :
    Duality.bregman entropy (entropyGradient x) c x ≤ Real.log (1 / δ) := by
  rw [bregman_entropyGradient_eq hc hx]
  have hs : ∑ i, c i * Real.log δ ≤ ∑ i, c i * Real.log (x i) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (Real.log_le_log hδ (hbound i)) (hc.1 i)
  rw [← Finset.sum_mul, hc.2, one_mul] at hs
  rw [one_div, Real.log_inv]
  linarith [entropy_nonpos hc]

variable [Nonempty ι]

/-- The smallest coordinate of a vector over a finite nonempty index set. -/
noncomputable def minCoordinate (x : EuclideanSpace ℝ ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => x i)

theorem minCoordinate_le (x : EuclideanSpace ℝ ι) (i : ι) : minCoordinate x ≤ x i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem minCoordinate_pos {x : EuclideanSpace ℝ ι} (hx : ∀ i, 0 < x i) :
    0 < minCoordinate x := by
  unfold minCoordinate
  rw [Finset.lt_inf'_iff]
  exact fun i _ => hx i

/-- The exact comparator-radius estimate in the Shannon proposition. -/
theorem bregman_entropyGradient_le_radius {c x : EuclideanSpace ℝ ι}
    (hc : c ∈ simplex) (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) :
    Duality.bregman entropy (entropyGradient x) c x ≤ Real.log (1 / minCoordinate x) :=
  bregman_entropyGradient_le_log_inv hc hx (minCoordinate_pos hpos) (minCoordinate_le x)

/-- Uniform initialization has coordinate lower bound `1 / card`. -/
theorem uniform_pos (i : ι) : 0 < (uniform : EuclideanSpace ℝ ι) i := by
  simp only [uniform_apply]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

@[simp] theorem minCoordinate_uniform :
    minCoordinate (uniform : EuclideanSpace ℝ ι) = (Fintype.card ι : ℝ)⁻¹ := by
  simp [minCoordinate, uniform]

@[simp] theorem radius_uniform :
    Real.log (1 / minCoordinate (uniform : EuclideanSpace ℝ ι)) =
      Real.log (Fintype.card ι : ℝ) := by simp

/-- A multiplicative-weights step for a loss vector. -/
noncomputable def multiplicativeWeights (x a : EuclideanSpace ℝ ι) (η : ℝ) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => x i * Real.exp (-η * a i) /
    ∑ j, x j * Real.exp (-η * a j))

@[simp] theorem multiplicativeWeights_apply (x a : EuclideanSpace ℝ ι) (η : ℝ) (i : ι) :
    multiplicativeWeights x a η i = x i * Real.exp (-η * a i) /
      ∑ j, x j * Real.exp (-η * a j) := rfl

/-- The maximizing player uses the positive-exponent version of the update. -/
@[simp] theorem multiplicativeWeights_neg_apply
    (x a : EuclideanSpace ℝ ι) (η : ℝ) (i : ι) :
    multiplicativeWeights x (-a) η i = x i * Real.exp (η * a i) /
      ∑ j, x j * Real.exp (η * a j) := by
  simp only [multiplicativeWeights_apply, PiLp.neg_apply, neg_mul_neg]

/-- A dual additive update is precisely the normalized multiplicative update. -/
theorem softmax_sub_smul (u a : EuclideanSpace ℝ ι) (η : ℝ) :
    softmax (u - η • a) = multiplicativeWeights (softmax u) a η := by
  have hs : (∑ j, Real.exp (u j)) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun i _ => Real.exp_pos (u i)) Finset.univ_nonempty)
  have ht : (∑ j, Real.exp (u j) * Real.exp (-η * a j)) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (Real.exp_pos _))
      Finset.univ_nonempty)
  ext i
  simp only [softmax_apply, multiplicativeWeights_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  simp only [sub_eq_add_neg, Real.exp_add]
  have hd : ∑ j, Real.exp (u j) / (∑ k, Real.exp (u k)) * Real.exp (-η * a j) =
      (∑ j, Real.exp (u j) * Real.exp (-η * a j)) / (∑ k, Real.exp (u k)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [neg_mul] at hd ht ⊢
  rw [hd]
  field_simp [hs, ht] <;> ring

/-- Positive probability vectors are softmax vectors with logarithmic dual coordinates. -/
theorem softmax_log {x : EuclideanSpace ℝ ι} (hx : x ∈ simplex)
    (hpos : ∀ i, 0 < x i) :
    softmax (WithLp.toLp 2 (fun i => Real.log (x i))) = x := by
  ext i
  simp only [softmax_apply, Real.exp_log (hpos _)]
  rw [hx.2, div_one]

/-- The radius is nonnegative for every strictly positive probability vector. -/
theorem radius_nonneg {x : EuclideanSpace ℝ ι} (hx : x ∈ simplex)
    (hpos : ∀ i, 0 < x i) : 0 ≤ Real.log (1 / minCoordinate x) := by
  rw [one_div, Real.log_inv]
  apply neg_nonneg.mpr
  exact Real.log_nonpos (minCoordinate_pos hpos).le
    ((minCoordinate_le x (Classical.arbitrary ι)).trans
      (coordinate_le_one hx (Classical.arbitrary ι)))

/-- Positive weights remain positive after a multiplicative update. -/
theorem multiplicativeWeights_pos {x : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 < x i) (a : EuclideanSpace ℝ ι) (η : ℝ) (i : ι) :
    0 < multiplicativeWeights x a η i := by
  exact div_pos (mul_pos (hx i) (Real.exp_pos _))
    (Finset.sum_pos (fun j _ => mul_pos (hx j) (Real.exp_pos _)) Finset.univ_nonempty)

/-- A multiplicative update is normalized to the simplex. -/
theorem multiplicativeWeights_mem_simplex {x : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 < x i) (a : EuclideanSpace ℝ ι) (η : ℝ) :
    multiplicativeWeights x a η ∈ simplex := by
  refine ⟨fun i => (multiplicativeWeights_pos hx a η i).le, ?_⟩
  simp only [multiplicativeWeights_apply, ← Finset.sum_div]
  exact div_self (ne_of_gt
    (Finset.sum_pos (fun j _ => mul_pos (hx j) (Real.exp_pos _)) Finset.univ_nonempty))

/-- The logarithmic dual representative realizes the multiplicative step. -/
theorem multiplicativeWeights_eq_softmax {x : EuclideanSpace ℝ ι}
    (hx : x ∈ simplex) (hpos : ∀ i, 0 < x i) (a : EuclideanSpace ℝ ι) (η : ℝ) :
    multiplicativeWeights x a η =
      softmax (WithLp.toLp 2 (fun i => Real.log (x i)) - η • a) := by
  rw [softmax_sub_smul, softmax_log hx hpos]

/-- Positive initialization and the update equations preserve feasibility and positivity. -/
theorem multiplicativeWeights_trajectory_mem {x loss : ℕ → EuclideanSpace ℝ ι}
    {η : ℝ} {T : ℕ} (hx0 : x 0 ∈ simplex) (hpos0 : ∀ i, 0 < x 0 i)
    (hstep : ∀ k < T, x (k + 1) = multiplicativeWeights (x k) (loss k) η) :
    ∀ k ≤ T, x k ∈ simplex ∧ ∀ i, 0 < x k i := by
  intro k hk
  induction k with
  | zero => exact ⟨hx0, hpos0⟩
  | succ k ih =>
    have hprev := ih (by omega)
    rw [hstep k (by omega)]
    exact ⟨multiplicativeWeights_mem_simplex hprev.2 _ _,
      multiplicativeWeights_pos hprev.2 _ _⟩

end AltOMD.Shannon
