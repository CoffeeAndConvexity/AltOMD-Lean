import AltOMD.Algebra.BCHLie
import AltOMD.Algebra.DynkinFormula

/-!
# The formal Baker–Campbell–Hausdorff theorem

This is the public entry point for Proposition A.1 of the manuscript.
It states the formal exponential identity with uniqueness, identifies the
universal homogeneous Lie coefficients `BCH.Phi`, and exposes their
explicit finite Dynkin formula. The theorem `BCH.propositionA1` bundles all
these assertions for the same coefficient sequence.

`NoncommutativeSeries.universalCoefficient_isLie` proves Lie membership in
every degree. This entry point depends only on algebraic modules; it does not
import the AltOMD analytic or regret developments. The project-specific
canonical coefficient interfaces are in the separate `AltOMD.Hamiltonian.BCHTheorem`.

The coefficient algebra is the free associative algebra over `ℚ` on two
letters. The outer power-series variable records word degree: the coefficient
of degree `q` is a homogeneous word polynomial of degree `q`. This models the
word-degree completion in the manuscript without evaluating an infinite sum
at arbitrary algebra elements. All identities are formal and coefficientwise.
-/

namespace AltOMD.BCH

open NoncommutativeSeries DynkinProjection

noncomputable section

/-- The free associative rational algebra on the two manuscript generators. -/
abbrev UniversalAlgebra := FreeAlgebra ℚ Bool

/-- The first free generator. -/
def U : UniversalAlgebra := FreeAlgebra.ι ℚ true

/-- The second free generator. -/
def V : UniversalAlgebra := FreeAlgebra.ι ℚ false

/-- The universal BCH series; the formal parameter records total word degree. -/
def Z : PowerSeries UniversalAlgebra :=
  bch (PowerSeries.monomial 1 U) (PowerSeries.monomial 1 V)

/-- The degree-`q` polynomial `Φ_q(U,V)` in Proposition A.1. -/
abbrev Phi (q : ℕ) : UniversalAlgebra := universalCoefficient q

/-- The formal exponential product has a unique logarithm with zero constant
term in every associative rational algebra. -/
theorem existsUnique_bch {A : Type*} [Ring A] [Algebra ℚ A]
    (p q : PowerSeries A) (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0) :
    ∃! z : PowerSeries A,
      z.constantCoeff = 0 ∧ expOf z = expOf p * expOf q := by
  refine ⟨bch p q, ⟨constantCoeff_bch p q, expOf_bch p q hp hq⟩, ?_⟩
  intro z hz
  exact expOf_injective hz.1 (constantCoeff_bch p q)
    (hz.2.trans (expOf_bch p q hp hq).symm)

/-- The defining formal logarithm in Proposition A.1. -/
theorem Z_eq_log :
    Z = logOf
      (expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V)) := rfl

/-- The coefficients of `Z` are exactly the universal polynomials `Φ_q`. -/
theorem coeff_Z (q : ℕ) : PowerSeries.coeff q Z = Phi q := rfl

@[simp] theorem Z_constantCoeff : Z.constantCoeff = 0 :=
  constantCoeff_bch _ _

/-- The formal identity `exp Z = exp U exp V`, with degree tracked explicitly. -/
theorem exp_Z :
    expOf Z =
      expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V) :=
  expOf_bch _ _ (by simp) (by simp)

/-- Uniqueness requires only the exponential identity and zero constant term. -/
theorem Z_unique {z : PowerSeries UniversalAlgebra}
    (hz : z.constantCoeff = 0)
    (he : expOf z =
      expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V)) :
    z = Z :=
  expOf_injective hz Z_constantCoeff (he.trans exp_Z.symm)

/-- Every word in `Φ_q` has length `q`. -/
theorem Phi_homogeneous (q : ℕ) : Homogeneous q (Phi q) :=
  universalCoefficient_homogeneous q

/-- Every `Φ_q` is a rational Lie polynomial in the two free generators. -/
theorem Phi_isLie (q : ℕ) : IsLie (Phi q) :=
  universalCoefficient_isLie q

/-- The fixed-degree Dynkin formula in Proposition A.1. Its transparent
right-hand side enumerates positive block lengths and all factorial-weighted
splits of each block into first-generator and second-generator letters. -/
theorem Phi_eq_dynkin (q : ℕ) (hq : 0 < q) :
    Phi q = DynkinFormula.explicitCoefficient q :=
  DynkinFormula.universalCoefficient_eq_dynkin q hq

/-- Proposition A.1: one universal series has zero constant term, satisfies
the exponential identity uniquely, equals the formal logarithm, and has the
homogeneous rational Lie coefficients given by the explicit Dynkin formula.

The formal variable records total word degree. The first and second inputs
are therefore `monomial 1 U` and `monomial 1 V`, rather than constant series.
The uniqueness clause imposes only zero constant term and the exponential
identity; it does not presuppose the formula or Lie membership. -/
theorem propositionA1 :
    Z.constantCoeff = 0 ∧
    expOf Z =
      expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V) ∧
    (∀ z : PowerSeries UniversalAlgebra,
      z.constantCoeff = 0 →
      expOf z =
        expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V) →
      z = Z) ∧
    Z = logOf
      (expOf (PowerSeries.monomial 1 U) * expOf (PowerSeries.monomial 1 V)) ∧
    (∀ q : ℕ, PowerSeries.coeff q Z = Phi q) ∧
    (∀ q : ℕ, Homogeneous q (Phi q) ∧ IsLie (Phi q)) ∧
    (∀ q : ℕ, 0 < q → Phi q = DynkinFormula.explicitCoefficient q) := by
  refine ⟨Z_constantCoeff, exp_Z, ?_, Z_eq_log, coeff_Z, ?_, Phi_eq_dynkin⟩
  · intro z hz he
    exact Z_unique hz he
  · intro q
    exact ⟨Phi_homogeneous q, Phi_isLie q⟩

end

end AltOMD.BCH
