import AltOMD.Algebra.DynkinGrading
import AltOMD.Algebra.NoncommutativeMap

/-!
# Word homogeneity of universal BCH coefficients

The formal-series index agrees with ordinary word length under sums,
products, and scalar formal exponential/logarithm. This proves ordinary
homogeneity of the associative BCH coefficients without assuming that they
are Lie polynomials.
-/

namespace AltOMD.DynkinProjection

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

def wordDegreeSubmodule (n : ℕ) : Submodule R (FreeAlgebra R ι) where
  carrier := {p | Homogeneous n p}
  zero_mem' := Homogeneous.zero n
  add_mem' := Homogeneous.add
  smul_mem' := by intro r p hp; exact hp.smul r

/-- Ordinary word homogeneity, coefficient by coefficient. -/
def HomogeneousSeries (p : PowerSeries (FreeAlgebra R ι)) : Prop :=
  ∀ n, Homogeneous n (PowerSeries.coeff n p)

theorem HomogeneousSeries.zero : HomogeneousSeries (0 : PowerSeries (FreeAlgebra R ι)) := by
  intro n
  simpa using Homogeneous.zero (R := R) (ι := ι) n

theorem HomogeneousSeries.one : HomogeneousSeries (1 : PowerSeries (FreeAlgebra R ι)) := by
  intro n
  cases n with
  | zero => simpa using homogeneous_word (R := R) ([] : List ι)
  | succ n => simpa using Homogeneous.zero (R := R) (ι := ι) (n + 1)

theorem HomogeneousSeries.add {p q : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) (hq : HomogeneousSeries q) : HomogeneousSeries (p + q) := by
  intro n
  simpa using Homogeneous.add (hp n) (hq n)

theorem HomogeneousSeries.smul (c : R) {p : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) : HomogeneousSeries (c • p) := by
  intro n
  simpa using (hp n).smul c

theorem HomogeneousSeries.neg {p : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) : HomogeneousSeries (-p) := by
  simpa using HomogeneousSeries.smul (-1 : R) hp

theorem HomogeneousSeries.sub {p q : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) (hq : HomogeneousSeries q) : HomogeneousSeries (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem HomogeneousSeries.mul {p q : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) (hq : HomogeneousSeries q) : HomogeneousSeries (p * q) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply (wordDegreeSubmodule (R := R) (ι := ι) n).sum_mem
  intro ij hij
  change Homogeneous n _
  simpa only [Finset.mem_antidiagonal.mp hij] using Homogeneous.mul (hp ij.1) (hq ij.2)

theorem HomogeneousSeries.pow {p : PowerSeries (FreeAlgebra R ι)}
    (hp : HomogeneousSeries p) (k : ℕ) : HomogeneousSeries (p ^ k) := by
  induction k with
  | zero => simpa using (HomogeneousSeries.one (R := R) (ι := ι))
  | succ k ih => simpa only [pow_succ] using ih.mul hp

theorem HomogeneousSeries.monomial {n : ℕ} {a : FreeAlgebra R ι}
    (ha : Homogeneous n a) : HomogeneousSeries (PowerSeries.monomial n a) := by
  intro k
  by_cases h : k = n
  · subst k; simpa using ha
  · simpa [PowerSeries.coeff_monomial, h] using Homogeneous.zero (R := R) (ι := ι) k

section Rational

open NoncommutativeSeries

variable {p q : PowerSeries (FreeAlgebra ℚ ι)}

theorem HomogeneousSeries.eval (hp : HomogeneousSeries p) (g : PowerSeries ℚ) :
    HomogeneousSeries (NoncommutativeSeries.eval p g) := by
  intro n
  rw [coeff_eval_eq_sum]
  apply (wordDegreeSubmodule (R := ℚ) (ι := ι) n).sum_mem
  intro k hk
  exact (hp.pow k n).smul _

theorem HomogeneousSeries.expOf (hp : HomogeneousSeries p) :
    HomogeneousSeries (expOf p) := hp.eval _

theorem HomogeneousSeries.logOf (hp : HomogeneousSeries p) :
    HomogeneousSeries (logOf p) := (hp.sub HomogeneousSeries.one).eval _

theorem HomogeneousSeries.bch (hp : HomogeneousSeries p) (hq : HomogeneousSeries q) :
    HomogeneousSeries (bch p q) := (hp.expOf.mul hq.expOf).logOf

end Rational

end
end AltOMD.DynkinProjection

namespace AltOMD.NoncommutativeSeries

open DynkinProjection

/-- Ordinary word homogeneity of every universal associative BCH coefficient.
This property is proved independently of Lie membership. -/
theorem universalCoefficient_homogeneous (n : ℕ) :
    Homogeneous n (universalCoefficient n) := by
  have hx : HomogeneousSeries (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ true)) :=
    HomogeneousSeries.monomial (by simpa using homogeneous_word (R := ℚ) [true])
  have hy : HomogeneousSeries (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ false)) :=
    HomogeneousSeries.monomial (by simpa using homogeneous_word (R := ℚ) [false])
  exact hx.bch hy n

end AltOMD.NoncommutativeSeries
