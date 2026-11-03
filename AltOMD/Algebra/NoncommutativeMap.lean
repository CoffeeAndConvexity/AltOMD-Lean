import AltOMD.Algebra.NoncommutativeRescale
import Mathlib.Algebra.FreeAlgebra

/-!
# Naturality and universal associative BCH coefficients

Formal scalar substitution commutes with homomorphisms of rational algebras.
The associative BCH coefficients can therefore be defined once in the free
algebra on two letters and evaluated in any rational algebra.
-/

namespace AltOMD.NoncommutativeSeries

open scoped BigOperators

noncomputable section

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem map_eval (f : A →ₐ[ℚ] B) (p : PowerSeries A) (g : PowerSeries ℚ) :
    PowerSeries.mapAlgHom f (eval p g) = eval (PowerSeries.mapAlgHom f p) g := by
  ext n
  rw [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  change f (PowerSeries.coeff n (eval p g)) = _
  rw [coeff_eval_eq_sum, map_sum, coeff_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, ← map_pow]
  simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  rfl

theorem map_expOf (f : A →ₐ[ℚ] B) (p : PowerSeries A) :
    PowerSeries.mapAlgHom f (expOf p) = expOf (PowerSeries.mapAlgHom f p) :=
  map_eval f p _

theorem map_logOf (f : A →ₐ[ℚ] B) (p : PowerSeries A) :
    PowerSeries.mapAlgHom f (logOf p) = logOf (PowerSeries.mapAlgHom f p) := by
  simp only [logOf, map_eval, map_sub, map_one]

theorem map_bch (f : A →ₐ[ℚ] B) (p q : PowerSeries A) :
    PowerSeries.mapAlgHom f (bch p q) =
      bch (PowerSeries.mapAlgHom f p) (PowerSeries.mapAlgHom f q) := by
  simp only [bch, map_logOf, map_mul, map_expOf]

@[simp] theorem mapAlgHom_monomial (f : A →ₐ[ℚ] B) (n : ℕ) (a : A) :
    PowerSeries.mapAlgHom f (PowerSeries.monomial n a) =
      PowerSeries.monomial n (f a) := by
  ext k
  simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, PowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem map_bchCoefficient (f : A →ₐ[ℚ] B) (n : ℕ) (a b : A) :
    f (bchCoefficient n a b) = bchCoefficient n (f a) (f b) := by
  have h := congrArg (PowerSeries.coeff n)
    (map_bch f (PowerSeries.monomial 1 a) (PowerSeries.monomial 1 b))
  rw [mapAlgHom_monomial, mapAlgHom_monomial] at h
  simpa only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map,
    AlgHom.coe_toRingHom, bchCoefficient] using h

/-- The universal associative BCH coefficient over the rationals.
This definition does not yet assert that it is a Lie polynomial. -/
def universalCoefficient (n : ℕ) : FreeAlgebra ℚ Bool :=
  bchCoefficient n (FreeAlgebra.ι ℚ true) (FreeAlgebra.ι ℚ false)

/-- Every associative BCH coefficient is obtained by substituting its two
generators into the universal coefficient. -/
theorem lift_universalCoefficient (n : ℕ) (a b : A) :
    FreeAlgebra.lift ℚ (fun letter : Bool => if letter then a else b)
      (universalCoefficient n) = bchCoefficient n a b := by
  rw [universalCoefficient, map_bchCoefficient]
  simp

end
end AltOMD.NoncommutativeSeries
