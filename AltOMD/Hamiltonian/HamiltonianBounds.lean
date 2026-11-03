import AltOMD.Hamiltonian.BracketBounds
import AltOMD.Hamiltonian.WordCoefficients

/-!
# Analytic bounds for the actual Hamiltonian corrections

The word coefficients are constructed in `WordCoefficients`; this module
evaluates their nested brackets on smooth scalar functions and bounds their
derivatives. Bounds on the values of the two individual Hamiltonians are not
required.
-/

noncomputable section

open scoped ContDiff

namespace AltOMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of an iterated derivative is linear on smooth functions. -/
def smoothDerivative (s : ℕ) (x : E) :
    SmoothScalar E →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ where
  toFun f := iteratedFDeriv ℝ s (f : E → ℝ) x
  map_add' := by
    intro f g
    exact iteratedFDeriv_add_apply (i := s)
      ((f.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)).contDiffAt)
      ((g.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)).contDiffAt)
  map_smul' := by
    intro c f
    exact iteratedFDeriv_const_smul_apply (i := s)
      ((f.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl s)).contDiffAt)

@[simp] theorem smoothDerivative_apply (s : ℕ) (x : E) (f : SmoothScalar E) :
    smoothDerivative s x f = iteratedFDeriv ℝ s (f : E → ℝ) x := rfl

theorem norm_iteratedFDeriv_poissonBracket_swap
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (f g : E → ℝ) (s : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ s (poissonBracket J f g) x‖ =
      ‖iteratedFDeriv ℝ s (poissonBracket J g f) x‖ := by
  have heq : poissonBracket J f g = -poissonBracket J g f :=
    funext (poissonBracket_antisymm J hJ f g)
  rw [heq, iteratedFDeriv_neg_apply, norm_neg]

open WordCoefficients

/-- Every nontrivial nested word satisfies the strong derivative estimate.
For a single leaf, the derivative order must be positive. -/
theorem norm_smoothDerivative_nestedHamiltonian_le
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x F‖ ≤ K ^ r * r.factorial)
    (w : Word) (s : ℕ) (x : E) (hw : 1 ≤ w.length)
    (hs : 1 < w.length ∨ 0 < s) :
    ‖smoothDerivative s x (nestedHamiltonian (smoothPoissonBracket J) G F w)‖ ≤
      bracketConstant J K ^ (w.length - 1) * (2 * K) ^ s *
        (w.length - 1 + s).factorial := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hC : 0 ≤ bracketConstant J K := by unfold bracketConstant; positivity
  have hcoef : 8 * ‖J‖ * K ^ 2 ≤ bracketConstant J K := by
    have hmax : 0 ≤ max ‖J‖ 1 := le_trans zero_le_one (le_max_right _ _)
    unfold bracketConstant
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left ‖J‖ 1) (sq_nonneg K),
      mul_nonneg hmax (sq_nonneg K)]
  induction w generalizing s with
  | nil => simp at hw
  | cons b w ih =>
    cases w with
    | nil =>
      have hspos : 1 ≤ s := by simp only [List.length_cons, List.length_nil] at hs; omega
      have hleaf : ‖smoothDerivative s x (if b then G else F)‖ ≤ K ^ s * s.factorial := by
        cases b
        · exact hF s x hspos
        · exact hG s x hspos
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self,
        pow_zero, one_mul, nestedHamiltonian]
      apply hleaf.trans
      gcongr
      linarith
    | cons c w =>
      have hleaf : ∀ r, 1 ≤ r →
          ‖iteratedFDeriv ℝ r ((if b then G else F : SmoothScalar E) : E → ℝ) x‖ ≤
            K ^ r * r.factorial := by
        intro r hr
        cases b
        · exact hF r x hr
        · exact hG r x hr
      have hinner : ∀ r, 1 ≤ r →
          ‖iteratedFDeriv ℝ r
            ((nestedHamiltonian (smoothPoissonBracket J) G F (c :: w) : SmoothScalar E) : E → ℝ) x‖ ≤
          bracketConstant J K ^ w.length * (2 * K) ^ r * (w.length + r).factorial := by
        intro r hr
        simpa only [List.length_cons, Nat.add_sub_cancel, smoothDerivative_apply] using
          ih r (by simp) (Or.inr (by omega))
      have hstep := norm_iteratedFDeriv_poissonBracket_step_le J
        (if b then G else F : SmoothScalar E).contDiff
        (nestedHamiltonian (smoothPoissonBracket J) G F (c :: w)).contDiff
        hC hK0 w.length s x hleaf hinner
      change ‖iteratedFDeriv ℝ s (poissonBracket J
          (nestedHamiltonian (smoothPoissonBracket J) G F (c :: w) : SmoothScalar E)
          (if b then G else F : SmoothScalar E)) x‖ ≤ _
      rw [norm_iteratedFDeriv_poissonBracket_swap J hJ]
      apply hstep.trans
      have hidx : (b :: c :: w).length - 1 = w.length + 1 := by simp
      rw [hidx, pow_succ (bracketConstant J K) w.length]
      have hfac : w.length + s + 1 = w.length + 1 + s := by omega
      rw [hfac]
      nlinarith [mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ bracketConstant J K ^ w.length * (2 * K) ^ s *
          ((w.length + 1 + s).factorial : ℝ) by positivity)]

/-- A finite word representation is controlled by its coefficient mass. -/
theorem norm_evaluateNested_linear_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : SmoothScalar E →ₗ[ℝ] SmoothScalar E →ₗ[ℝ] SmoothScalar E)
    (G F : SmoothScalar E) (D : SmoothScalar E →ₗ[ℝ] V)
    (p : Polynomial) {M : ℝ}
    (hword : ∀ t ∈ p, ‖D (nestedHamiltonian B G F t.2)‖ ≤ M) :
    ‖D (evaluateNested B G F p)‖ ≤ mass p * M := by
  induction p with
  | nil => simp [evaluateNested, mass]
  | cons t p ih =>
    have ht := hword t (by simp)
    have hp := ih (fun u hu => hword u (by simp [hu]))
    simp only [evaluateNested, map_add, map_smul]
    calc
      ‖t.1 • D (nestedHamiltonian B G F t.2) + D (evaluateNested B G F p)‖ ≤
          ‖t.1 • D (nestedHamiltonian B G F t.2)‖ + ‖D (evaluateNested B G F p)‖ :=
            norm_add_le _ _
      _ = |t.1| * ‖D (nestedHamiltonian B G F t.2)‖ + ‖D (evaluateNested B G F p)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t.1| * M + mass p * M := by gcongr
      _ = mass (t :: p) * M := by simp only [mass]; ring

/-- A homogeneous word polynomial inherits the factorial bracket bound. -/
theorem norm_smoothDerivative_evaluateNested_le
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x F‖ ≤ K ^ r * r.factorial)
    (p : Polynomial) (q s : ℕ) (x : E) (hp : Homogeneous q p)
    (hq : 1 ≤ q) (hqs : 1 < q ∨ 0 < s) :
    ‖smoothDerivative s x (evaluateNested (smoothPoissonBracket J) G F p)‖ ≤
      mass p * (bracketConstant J K ^ (q - 1) * (2 * K) ^ s *
        (q - 1 + s).factorial) := by
  apply norm_evaluateNested_linear_le
  intro t ht
  have hlen := hp t ht
  simpa only [hlen] using norm_smoothDerivative_nestedHamiltonian_le J hJ G F hK hG hF
    t.2 s x (by omega) (by omega)

/-- Derivatives and mixed Lie iterates of the actual BCH Hamiltonian coefficients.
The sole algebraic input is the classical DSW representation; its coefficient
mass bound and every analytic estimate are proved in this development. -/
theorem norm_smoothDerivative_mixed_correction_le
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x F‖ ≤ K ^ r * r.factorial)
    (Z : ℕ → FormalEnergy.LieExpression) (dsw : ClassicalDSWInput Z (SmoothScalar E))
    (r α β s : ℕ) (x : E) (hpositive : 0 < r + α + β + s) :
    ‖smoothDerivative s x
      ((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
        (FormalEnergy.correctedHamiltonian (smoothPoissonBracket J) G F Z r))‖ ≤
      (4 * bracketConstant J K) ^ (r + α + β + s + 1) *
        (r + α + β + s).factorial := by
  obtain ⟨hrep, hhom, hmass⟩ := correction_representation_and_bound Z dsw
    (smoothPoissonBracket J) (smoothPoissonBracket_antisymm J hJ)
    (smoothPoissonBracket_jacobi J hJ) G F r
  let p := prepend 1 (List.replicate α true ++ List.replicate β false)
    (correctionRepresentation r)
  have hp : Homogeneous (α + β + (r + 1)) p := by
    simpa only [p, List.length_append, List.length_replicate] using
      homogeneous_prefix (r + 1) 1 (List.replicate α true ++ List.replicate β false)
        (correctionRepresentation r) hhom
  have hp_mass : mass p ≤ (4 : ℝ) ^ (r + 1) := by
    simpa only [p, mass_prefix, abs_one, one_mul] using hmass
  have hbound := norm_smoothDerivative_evaluateNested_le J hJ G F hK hG hF
    p (α + β + (r + 1)) s x hp (by omega) (by omega)
  have hindex : α + β + (r + 1) - 1 = r + α + β := by omega
  rw [hindex] at hbound
  rw [hrep]
  change ‖smoothDerivative s x
      (((smoothPoissonBracket J).flip G ^ α * (smoothPoissonBracket J).flip F ^ β)
        (evaluateNested (smoothPoissonBracket J) G F (correctionRepresentation r)))‖ ≤ _
  rw [evaluateNested_mixed_powers (smoothPoissonBracket J) G F
    (correctionRepresentation r) (by omega) hhom α β]
  apply hbound.trans
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hmax : 1 ≤ max ‖J‖ 1 := le_max_right _ _
  have hC1 : 1 ≤ bracketConstant J K := by
    unfold bracketConstant
    nlinarith [sq_nonneg (K - 1), mul_le_mul_of_nonneg_right hmax (sq_nonneg K)]
  have hC0 : 0 ≤ bracketConstant J K := le_trans zero_le_one hC1
  have hscale : 2 * K ≤ bracketConstant J K := by
    unfold bracketConstant
    nlinarith [sq_nonneg (K - 1), mul_le_mul_of_nonneg_right hmax (sq_nonneg K)]
  calc
    mass p * (bracketConstant J K ^ (r + α + β) * (2 * K) ^ s *
        (r + α + β + s).factorial) ≤
        (4 : ℝ) ^ (r + 1) *
          (bracketConstant J K ^ (r + α + β) * bracketConstant J K ^ s *
            (r + α + β + s).factorial) := by gcongr
    _ = (4 : ℝ) ^ (r + 1) * bracketConstant J K ^ (r + α + β + s) *
        (r + α + β + s).factorial := by rw [pow_add]; ring
    _ ≤ (4 : ℝ) ^ (r + α + β + s + 1) *
        bracketConstant J K ^ (r + α + β + s + 1) *
          (r + α + β + s).factorial := by
      have hfour : (4 : ℝ) ^ (r + 1) ≤ (4 : ℝ) ^ (r + α + β + s + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hpower : bracketConstant J K ^ (r + α + β + s) ≤
          bracketConstant J K ^ (r + α + β + s + 1) :=
        pow_le_pow_right₀ hC1 (by omega)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hfour hpower (by positivity) (by positivity)) (by positivity)
    _ = (4 * bracketConstant J K) ^ (r + α + β + s + 1) *
        (r + α + β + s).factorial := by rw [mul_pow]

/-- The mixed Lie derivative estimate used in the Taylor remainder. -/
theorem norm_mixed_correction_le
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ r x, 1 ≤ r → ‖smoothDerivative r x G‖ ≤ K ^ r * r.factorial)
    (hF : ∀ r x, 1 ≤ r → ‖smoothDerivative r x F‖ ≤ K ^ r * r.factorial)
    (Z : ℕ → FormalEnergy.LieExpression) (dsw : ClassicalDSWInput Z (SmoothScalar E))
    (r α β : ℕ) (x : E) (hpositive : 0 < r + α + β) :
    ‖(((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
      (FormalEnergy.correctedHamiltonian (smoothPoissonBracket J) G F Z r)) : E → ℝ) x‖ ≤
      (4 * bracketConstant J K) ^ (r + α + β + 1) * (r + α + β).factorial := by
  simpa only [Nat.add_zero, smoothDerivative_apply, norm_iteratedFDeriv_zero] using
    norm_smoothDerivative_mixed_correction_le J hJ G F hK hG hF Z dsw
      r α β 0 x (by simpa using hpositive)

/-- The zeroth coefficient is identified separately; no bound on `F(x)` or `G(x)` is used. -/
theorem smooth_correction_zero
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (G F : SmoothScalar E)
    (Z : ℕ → FormalEnergy.LieExpression)
    (bch : FormalEnergy.ClassicalBCHInput Z (SmoothScalar E)) :
    FormalEnergy.correctedHamiltonian (smoothPoissonBracket J) G F Z 0 = F + G :=
  FormalEnergy.correctedHamiltonian_zero (smoothPoissonBracket J) G F Z bch

end AltOMD
