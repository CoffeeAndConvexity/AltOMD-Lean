import AltOMD.Hamiltonian.ScalarMajorant
import AltOMD.Hamiltonian.CanonicalHamiltonian
import AltOMD.Hamiltonian.HamiltonianBounds

/-! Global nested-bracket and canonical-correction bounds in manuscript form. -/

noncomputable section
open scoped ContDiff

namespace AltOMD.ManuscriptBounds

open AltOMD WordCoefficients ScalarMajorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordinary right nesting: the first letter is the outer left argument. -/
def rightNested (J : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G F : SmoothScalar E) (w : Word) : SmoothScalar E :=
  nestedHamiltonian (smoothPoissonBracket J).flip G F w

/-- Opposite-bracket recursion changes only a constant sign. -/
theorem norm_nested_eq_rightNested
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) (w : Word) (s : ℕ) (x : E) :
    ‖smoothDerivative s x (nestedHamiltonian (smoothPoissonBracket J) G F w)‖ =
      ‖smoothDerivative s x (rightNested J G F w)‖ := by
  have h := congrArg (fun Q : SmoothScalar E => ‖smoothDerivative s x Q‖)
    (CanonicalHamiltonian.nestedHamiltonian_eq_signed_flip (smoothPoissonBracket J)
      (smoothPoissonBracket_antisymm J hJ) G F w)
  simpa only [rightNested, map_smul, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_neg, abs_one, one_pow, one_mul] using h

/-- The exact factorial bound, from the summed standing regularity assumption.
The output also proves that the real supremum is finite. -/
theorem nested_bracket_bound
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ a, 1 ≤ a → ∀ x y,
      ‖smoothDerivative a x F‖ + ‖smoothDerivative a y G‖ ≤ K ^ a * a.factorial)
    (w : Word) (hw : 2 ≤ w.length) (s : ℕ) :
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (rightNested J G F w : E → ℝ) x‖) ∧
      derivativeSup (rightNested J G F w : E → ℝ) s /
        ((w.length + s - 1).factorial : ℝ) ≤
          bracketConstant J K ^ (w.length + s - 1) := by
  have hF : ∀ a x, 1 ≤ a → ‖smoothDerivative a x F‖ ≤ K ^ a * a.factorial := by
    intro a x ha
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hregularity a ha x 0)
  have hG : ∀ a y, 1 ≤ a → ‖smoothDerivative a y G‖ ≤ K ^ a * a.factorial := by
    intro a y ha
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hregularity a ha 0 y)
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hC0 : 0 ≤ bracketConstant J K := by unfold bracketConstant; positivity
  have hscale : 2 * K ≤ bracketConstant J K := by
    have hmax : 1 ≤ max ‖J‖ 1 := le_max_right _ _
    unfold bracketConstant
    nlinarith [sq_nonneg (K - 1),
      mul_le_mul_of_nonneg_right hmax (sq_nonneg K)]
  have hindex : w.length - 1 + s = w.length + s - 1 := by omega
  have hpoint (x : E) :
      ‖iteratedFDeriv ℝ s (rightNested J G F w : E → ℝ) x‖ ≤
        bracketConstant J K ^ (w.length + s - 1) *
          ((w.length + s - 1).factorial : ℝ) := by
    have h := norm_smoothDerivative_nestedHamiltonian_le J hJ G F hK hG hF
      w s x (by omega) (Or.inl (by omega))
    rw [norm_nested_eq_rightNested J hJ G F w s x] at h
    change ‖smoothDerivative s x (rightNested J G F w)‖ ≤ _
    apply h.trans
    calc
      bracketConstant J K ^ (w.length - 1) * (2 * K) ^ s *
          ((w.length - 1 + s).factorial : ℝ) ≤
        bracketConstant J K ^ (w.length - 1) * bracketConstant J K ^ s *
          ((w.length - 1 + s).factorial : ℝ) := by gcongr
      _ = _ := by rw [← pow_add, hindex]
  refine ⟨⟨bracketConstant J K ^ (w.length + s - 1) *
    ((w.length + s - 1).factorial : ℝ), ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hpoint x
  · exact (div_le_iff₀ (by positivity)).2
      (derivativeSup_le _ s _ hpoint)

/-- Canonical mixed Lie derivatives, under exactly the nontrivial nested-word
bound required by the manuscript argument. No BCH representation is a premise. -/
theorem canonical_mixed_pointwise_of_nested
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {C : ℝ} (hC : 1 ≤ C)
    (hbracket : ∀ (w : Word) (s : ℕ), 2 ≤ w.length →
      BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (rightNested J G F w : E → ℝ) x‖) ∧
        derivativeSup (rightNested J G F w : E → ℝ) s /
          ((w.length + s - 1).factorial : ℝ) ≤ C ^ (w.length + s - 1))
    (r α β : ℕ) (hp : 1 ≤ r + α + β) (x : E) :
    ‖(((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
      (CanonicalHamiltonian.correction (smoothPoissonBracket J) G F r)) : E → ℝ) x‖ ≤
      (4 * C) ^ (r + α + β + 1) * (r + α + β).factorial := by
  let p := prepend 1 (List.replicate α true ++ List.replicate β false)
    (correctionRepresentation r)
  have hhom : Homogeneous (α + β + (r + 1)) p := by
    simpa only [p, List.length_append, List.length_replicate] using
      homogeneous_prefix (r + 1) 1 (List.replicate α true ++ List.replicate β false)
        (correctionRepresentation r) (correctionRepresentation_homogeneous r)
  have hmass : mass p ≤ (4 : ℝ) ^ (r + 1) := by
    simpa only [p, mass_prefix, abs_one, one_mul] using correctionRepresentation_mass_le r
  have hword : ∀ t ∈ p,
      ‖smoothDerivative 0 x (nestedHamiltonian (smoothPoissonBracket J) G F t.2)‖ ≤
        C ^ (r + α + β) * (r + α + β).factorial := by
    intro t ht
    have hlen := hhom t ht
    have hw : 2 ≤ t.2.length := by omega
    obtain ⟨hbd, hs⟩ := hbracket t.2 0 hw
    have hpoint := norm_derivative_le_sup (rightNested J G F t.2 : E → ℝ) 0 hbd x
    have hsup := (div_le_iff₀ (by positivity : (0 : ℝ) < (t.2.length + 0 - 1).factorial)).mp hs
    have hidx : t.2.length + 0 - 1 = r + α + β := by omega
    rw [norm_nested_eq_rightNested J hJ G F t.2 0 x]
    change ‖iteratedFDeriv ℝ 0 (rightNested J G F t.2 : E → ℝ) x‖ ≤ _
    simpa only [hidx] using hpoint.trans hsup
  have hb := norm_evaluateNested_linear_le (smoothPoissonBracket J) G F
    (smoothDerivative 0 x) p hword
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hfinal : ‖smoothDerivative 0 x
      (evaluateNested (smoothPoissonBracket J) G F p)‖ ≤
      (4 * C) ^ (r + α + β + 1) * (r + α + β).factorial := by
    apply hb.trans
    calc
      mass p * (C ^ (r + α + β) * (r + α + β).factorial) ≤
        (4 : ℝ) ^ (r + 1) * (C ^ (r + α + β) * (r + α + β).factorial) := by gcongr
      _ ≤ (4 : ℝ) ^ (r + α + β + 1) *
          (C ^ (r + α + β + 1) * (r + α + β).factorial) := by
        have hfour : (4 : ℝ) ^ (r + 1) ≤ (4 : ℝ) ^ (r + α + β + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hpower : C ^ (r + α + β) ≤ C ^ (r + α + β + 1) :=
          pow_le_pow_right₀ hC (by omega)
        exact mul_le_mul hfour (mul_le_mul_of_nonneg_right hpower (by positivity))
          (by positivity) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have heval :
      (poissonGenerator J G ^ α * poissonGenerator J F ^ β)
        (CanonicalHamiltonian.correction (smoothPoissonBracket J) G F r) =
      evaluateNested (smoothPoissonBracket J) G F p := by
    rw [CanonicalHamiltonian.correction_eq_nested]
    change (((smoothPoissonBracket J).flip G ^ α * (smoothPoissonBracket J).flip F ^ β)
      (evaluateNested (smoothPoissonBracket J) G F (correctionRepresentation r))) = _
    exact evaluateNested_mixed_powers (smoothPoissonBracket J) G F
      (correctionRepresentation r) (by omega) (correctionRepresentation_homogeneous r) α β
  rw [heval]
  simpa only [smoothDerivative_apply, norm_iteratedFDeriv_zero] using hfinal

/-- The manuscript's global mixed Lie-derivative bound for canonical corrections,
with the nested-bracket lemma as the sole quantitative input. -/
theorem canonical_mixed_bound_of_nested
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {C : ℝ} (hC : 1 ≤ C)
    (hbracket : ∀ (w : Word) (s : ℕ), 2 ≤ w.length →
      BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (rightNested J G F w : E → ℝ) x‖) ∧
        derivativeSup (rightNested J G F w : E → ℝ) s /
          ((w.length + s - 1).factorial : ℝ) ≤ C ^ (w.length + s - 1))
    (r α β : ℕ) (hp : 1 ≤ r + α + β) :
    let Q := ((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
      (CanonicalHamiltonian.correction (smoothPoissonBracket J) G F r) : E → ℝ)
    BddAbove (Set.range fun x => |Q x|) ∧
      sSup (Set.range fun x => |Q x|) ≤
        (4 * C) ^ (r + α + β + 1) * (r + α + β).factorial := by
  dsimp only
  have hpoint := canonical_mixed_pointwise_of_nested J hJ G F hC hbracket r α β hp
  simp only [Real.norm_eq_abs] at hpoint
  refine ⟨⟨(4 * C) ^ (r + α + β + 1) * ((r + α + β).factorial : ℝ), ?_⟩,
    csSup_le (Set.range_nonempty _) ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hpoint x
  · rintro _ ⟨x, rfl⟩
    exact hpoint x

/-- The same canonical bound with the summed standing regularity assumption.
Both the nested-bracket premise and the BCH representation are supplied here. -/
theorem canonical_mixed_bound
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ a, 1 ≤ a → ∀ x y,
      ‖smoothDerivative a x F‖ + ‖smoothDerivative a y G‖ ≤ K ^ a * a.factorial)
    (r α β : ℕ) (hp : 1 ≤ r + α + β) :
    let Q := ((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
      (CanonicalHamiltonian.correction (smoothPoissonBracket J) G F r) : E → ℝ)
    BddAbove (Set.range fun x => |Q x|) ∧
      sSup (Set.range fun x => |Q x|) ≤
        (4 * bracketConstant J K) ^ (r + α + β + 1) * (r + α + β).factorial := by
  have hC : 1 ≤ bracketConstant J K := by
    have hmax : 1 ≤ max ‖J‖ 1 := le_max_right _ _
    unfold bracketConstant
    nlinarith [sq_nonneg (K - 1),
      mul_le_mul_of_nonneg_right hmax (sq_nonneg K)]
  exact canonical_mixed_bound_of_nested J hJ G F hC
    (fun w s hw => nested_bracket_bound J hJ G F hK hregularity w hw s) r α β hp

/-- The source nested-bracket bound under the literal summed global norm
assumption. Extended suprema require no separate boundedness hypotheses. -/
theorem nested_bracket_bound_source
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ a, 1 ≤ a →
      extendedDerivativeSup (F : E → ℝ) a + extendedDerivativeSup (G : E → ℝ) a ≤
        ((K ^ a * a.factorial : ℝ) : EReal))
    (w : Word) (hw : 2 ≤ w.length) (s : ℕ) :
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ s (rightNested J G F w : E → ℝ) x‖) ∧
      derivativeSup (rightNested J G F w : E → ℝ) s /
        ((w.length + s - 1).factorial : ℝ) ≤
          bracketConstant J K ^ (w.length + s - 1) := by
  have hpoint : ∀ a, 1 ≤ a → ∀ x y,
      ‖smoothDerivative a x F‖ + ‖smoothDerivative a y G‖ ≤ K ^ a * a.factorial := by
    intro a ha x y
    exact derivative_sum_le_of_extended (E := E) (F : E → ℝ) (G : E → ℝ)
      a (K ^ a * a.factorial) (hregularity a ha) x y
  exact nested_bracket_bound J hJ G F hK hpoint w hw s

/-- The canonical mixed bound from the same summed global norm assumption. -/
theorem canonical_mixed_bound_source
    (J : (E →L[ℝ] ℝ) →L[ℝ] E) (hJ : IsSkewPoissonTensor J)
    (G F : SmoothScalar E) {K : ℝ} (hK : 1 ≤ K)
    (hregularity : ∀ a, 1 ≤ a →
      extendedDerivativeSup (F : E → ℝ) a + extendedDerivativeSup (G : E → ℝ) a ≤
        ((K ^ a * a.factorial : ℝ) : EReal))
    (r α β : ℕ) (hp : 1 ≤ r + α + β) :
    let Q := ((poissonGenerator J G ^ α * poissonGenerator J F ^ β)
      (CanonicalHamiltonian.correction (smoothPoissonBracket J) G F r) : E → ℝ)
    BddAbove (Set.range fun x => |Q x|) ∧
      sSup (Set.range fun x => |Q x|) ≤
        (4 * bracketConstant J K) ^ (r + α + β + 1) * (r + α + β).factorial := by
  have hpoint : ∀ a, 1 ≤ a → ∀ x y,
      ‖smoothDerivative a x F‖ + ‖smoothDerivative a y G‖ ≤ K ^ a * a.factorial := by
    intro a ha x y
    exact derivative_sum_le_of_extended (E := E) (F : E → ℝ) (G : E → ℝ)
      a (K ^ a * a.factorial) (hregularity a ha) x y
  exact canonical_mixed_bound J hJ G F hK hpoint r α β hp

end AltOMD.ManuscriptBounds
