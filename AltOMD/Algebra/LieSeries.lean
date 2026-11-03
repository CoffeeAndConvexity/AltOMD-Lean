import AltOMD.Algebra.DynkinProjection
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Formal series with Lie-polynomial coefficients

The coefficients of a commutator of two such series are again Lie polynomials.
Substitution into a finite Lie polynomial preserves this property, as required
by the all-degree BCH induction. Products are never treated as commutative.
-/

namespace AltOMD.DynkinProjection

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The linear subspace of Lie polynomials inside the free associative algebra. -/
def lieSubmodule : Submodule R (FreeAlgebra R ι) where
  carrier := {p | IsLie p}
  zero_mem' := IsLie.zero
  add_mem' := IsLie.add
  smul_mem' := IsLie.smul

@[simp] theorem mem_lieSubmodule {p : FreeAlgebra R ι} :
    p ∈ lieSubmodule (R := R) (ι := ι) ↔ IsLie p := Iff.rfl

/-- Lie coefficients without a requirement tying their word degree to the
formal-series index. This is useful for truncated induction hypotheses. -/
def LieSeries (p : PowerSeries (FreeAlgebra R ι)) : Prop :=
  ∀ n, IsLie (PowerSeries.coeff n p)

theorem LieSeries.zero : LieSeries (0 : PowerSeries (FreeAlgebra R ι)) := by
  intro n
  simpa using (IsLie.zero (R := R) (ι := ι))

theorem LieSeries.add {p q : PowerSeries (FreeAlgebra R ι)}
    (hp : LieSeries p) (hq : LieSeries q) : LieSeries (p + q) := by
  intro n
  simpa using IsLie.add (hp n) (hq n)

theorem LieSeries.smul (c : R) {p : PowerSeries (FreeAlgebra R ι)}
    (hp : LieSeries p) : LieSeries (c • p) := by
  intro n
  simpa using IsLie.smul c (hp n)

theorem LieSeries.commutator {p q : PowerSeries (FreeAlgebra R ι)}
    (hp : LieSeries p) (hq : LieSeries q) : LieSeries (p * q - q * p) := by
  intro n
  rw [map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  have hswap : (∑ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 q * PowerSeries.coeff ij.2 p) =
      ∑ ij ∈ Finset.antidiagonal n,
        PowerSeries.coeff ij.2 q * PowerSeries.coeff ij.1 p := by
    simpa using (Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun ij => PowerSeries.coeff ij.1 q * PowerSeries.coeff ij.2 p)).symm
  rw [hswap, ← Finset.sum_sub_distrib]
  apply (lieSubmodule (R := R) (ι := ι)).sum_mem
  intro ij hij
  exact IsLie.commutator (hp ij.1) (hq ij.2)

/-- Substitution of series with Lie coefficients into a finite Lie polynomial
has Lie coefficients in every degree. -/
theorem IsLie.lieSeries_lift {κ : Type*} {p : FreeAlgebra R κ} (hp : IsLie p)
    (f : κ → PowerSeries (FreeAlgebra R ι)) (hf : ∀ i, LieSeries (f i)) :
    LieSeries (FreeAlgebra.lift R f p) := by
  induction hp with
  | zero => simpa using (LieSeries.zero (R := R) (ι := ι))
  | generator i => simpa using hf i
  | add hp hq ihp ihq => simpa using LieSeries.add ihp ihq
  | smul r hp ih => simpa using LieSeries.smul r ih
  | commutator hp hq ihp ihq =>
    simpa only [map_sub, map_mul] using LieSeries.commutator ihp ihq

/-- Truncating at the induction horizon gives a series all of whose
coefficients are Lie polynomials. -/
theorem lieSeries_trunc (p : PowerSeries (FreeAlgebra R ι)) (N : ℕ)
    (hp : ∀ n < N, IsLie (PowerSeries.coeff n p)) :
    LieSeries (PowerSeries.trunc N p : PowerSeries (FreeAlgebra R ι)) := by
  intro n
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · exact hp n h
  · exact IsLie.zero

/-- Substitution of Lie polynomials into a Lie polynomial preserves its
membership in the Lie span. -/
theorem IsLie.map {κ : Type*} {p : FreeAlgebra R κ} (hp : IsLie p)
    (f : κ → FreeAlgebra R ι) (hf : ∀ i, IsLie (f i)) :
    IsLie (FreeAlgebra.lift R f p) := by
  induction hp with
  | zero => simpa using (IsLie.zero (R := R) (ι := ι))
  | generator i => simpa using hf i
  | add hp hq ihp ihq => simpa using IsLie.add ihp ihq
  | smul r hp ih => simpa using IsLie.smul r ih
  | commutator hp hq ihp ihq =>
    simpa only [map_sub, map_mul] using IsLie.commutator ihp ihq

end
end AltOMD.DynkinProjection
