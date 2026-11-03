import AltOMD.Algebra.DynkinProjection
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Dynkin projection and ordinary word homogeneity

The Euler derivation multiplies each associative word by its length. On every
Lie polynomial it equals the right Dynkin map. Consequently the classical
Dynkin–Specht–Wever identity follows from Lie membership and ordinary word
support in a fixed degree, without requiring a graded presentation.
-/

namespace AltOMD.DynkinProjection

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

private def tangentLift : FreeAlgebra R ι →ₐ[R]
    TrivSqZeroExt (FreeAlgebra R ι) (FreeAlgebra R ι) :=
  FreeAlgebra.lift R (fun i => ((FreeAlgebra.ι R i, FreeAlgebra.ι R i) :
    TrivSqZeroExt (FreeAlgebra R ι) (FreeAlgebra R ι)))

private theorem tangentLift_generator (i : ι) :
    tangentLift (FreeAlgebra.ι R i) = (FreeAlgebra.ι R i, FreeAlgebra.ι R i) :=
  FreeAlgebra.lift_ι_apply (R := R) (A := TrivSqZeroExt (FreeAlgebra R ι)
    (FreeAlgebra R ι)) _ i

private theorem tangentLift_fst (p : FreeAlgebra R ι) : (tangentLift p).fst = p := by
  have h : (TrivSqZeroExt.fstHom R (FreeAlgebra R ι) (FreeAlgebra R ι)).comp
      tangentLift = AlgHom.id R (FreeAlgebra R ι) := by
    ext i
    change (tangentLift (FreeAlgebra.ι R i)).fst = FreeAlgebra.ι R i
    rw [tangentLift_generator]
    rfl
  exact AlgHom.congr_fun h p

/-- The Euler derivation, defined using the universal map into dual numbers. -/
def euler : FreeAlgebra R ι →ₗ[R] FreeAlgebra R ι where
  toFun p := (tangentLift p).snd
  map_add' p q := by simp
  map_smul' r p := by simp

@[simp] theorem euler_one : euler (1 : FreeAlgebra R ι) = 0 := by
  simp [euler]

@[simp] theorem euler_generator (i : ι) :
    euler (FreeAlgebra.ι R i) = FreeAlgebra.ι R i := by
  change (tangentLift (FreeAlgebra.ι R i)).snd = FreeAlgebra.ι R i
  rw [tangentLift_generator]
  rfl

/-- The ordinary Leibniz identity, valid for noncommuting polynomials. -/
theorem euler_mul (p q : FreeAlgebra R ι) :
    euler (p * q) = p * euler q + euler p * q := by
  change (tangentLift (p * q)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, tangentLift_fst, tangentLift_fst]
  rfl

@[simp] theorem euler_word (w : List ι) :
    euler (word (R := R) w) = (w.length : R) • word w := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [word_cons, euler_mul, euler_generator, ih]
      simp [Nat.cast_add, add_smul, add_comm]

/-- The Dynkin map equals the Euler derivation on every Lie polynomial,
including sums with terms of different degrees. -/
theorem dynkin_eq_euler_of_isLie {p : FreeAlgebra R ι} (hp : IsLie p) :
    dynkin p = euler p := by
  induction hp with
  | zero => simp
  | generator i => simp
  | add hp hq ihp ihq => simp [ihp, ihq]
  | smul r hp ih => simp [ih]
  | @commutator p q hp hq ihp ihq =>
      rw [map_sub, dynkin_mul_of_isLie hp q hq.augmentation_eq_zero,
        dynkin_mul_of_isLie hq p hp.augmentation_eq_zero, ihp, ihq,
        map_sub, euler_mul, euler_mul]
      abel

private abbrev monoidEquiv :
    FreeAlgebra R ι ≃ₐ[R] MonoidAlgebra R (FreeMonoid ι) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid

/-- The ordinary associative word coefficients of a free-algebra element. -/
def wordCoefficients : FreeAlgebra R ι ≃ₗ[R] (FreeMonoid ι →₀ R) :=
  monoidEquiv.toLinearEquiv.trans (MonoidAlgebra.coeffLinearEquiv R)

private theorem monoidEquiv_word (w : List ι) :
    monoidEquiv (word (R := R) w) = MonoidAlgebra.single (FreeMonoid.ofList w) 1 := by
  induction w with
  | nil =>
      change monoidEquiv (1 : FreeAlgebra R ι) = 1
      exact map_one _
  | cons i w ih =>
      rw [word_cons, map_mul, ih]
      change (FreeAlgebra.lift R
        (fun x => MonoidAlgebra.of R (FreeMonoid ι) (FreeMonoid.of x)))
          (FreeAlgebra.ι R i) * MonoidAlgebra.single (FreeMonoid.ofList w) 1 = _
      simp only [FreeAlgebra.lift_ι_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_mul_single, one_mul, FreeMonoid.ofList_cons]

@[simp] theorem wordCoefficients_word (w : List ι) :
    wordCoefficients (word (R := R) w) = Finsupp.single (FreeMonoid.ofList w) 1 := by
  change (monoidEquiv (word w)).coeff = _
  rw [monoidEquiv_word]
  rfl

/-- Reconstruction from the ordinary associative word coefficients. -/
theorem sum_wordCoefficients (p : FreeAlgebra R ι) :
    (wordCoefficients p).sum (fun w r => r • word (R := R) w.toList) = p := by
  calc
    _ = MonoidAlgebra.lift R (FreeAlgebra R ι) (FreeMonoid ι)
        (FreeMonoid.lift (FreeAlgebra.ι R)) (monoidEquiv p) := by
      rw [MonoidAlgebra.lift_apply]
      change (monoidEquiv p).coeff.sum (fun w r => r • word (R := R) w.toList) = _
      apply Finset.sum_congr rfl
      intro w hw
      change (monoidEquiv p).coeff w • word w.toList =
        (monoidEquiv p).coeff w • (FreeMonoid.lift (FreeAlgebra.ι R)) w
      rw [FreeMonoid.lift_apply]
      rfl
    _ = p := monoidEquiv.symm_apply_apply p

/-- Ordinary homogeneity: every coefficient outside word length `n` vanishes. -/
def Homogeneous (n : ℕ) (p : FreeAlgebra R ι) : Prop :=
  ∀ w : FreeMonoid ι, w.toList.length ≠ n → wordCoefficients p w = 0

theorem homogeneous_iff_support {n : ℕ} {p : FreeAlgebra R ι} :
    Homogeneous n p ↔ ∀ w ∈ (wordCoefficients p).support, w.toList.length = n := by
  classical
  constructor
  · intro hp w hw
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hw) (hp w hn)
  · intro hp w hn
    by_contra hw
    exact hn (hp w (Finsupp.mem_support_iff.mpr hw))

theorem Homogeneous.zero (n : ℕ) : Homogeneous n (0 : FreeAlgebra R ι) := by
  intro w hw
  simp

theorem Homogeneous.add {n : ℕ} {p q : FreeAlgebra R ι}
    (hp : Homogeneous n p) (hq : Homogeneous n q) : Homogeneous n (p + q) := by
  intro w hw
  simp [hp w hw, hq w hw]

theorem Homogeneous.smul {n : ℕ} {p : FreeAlgebra R ι}
    (hp : Homogeneous n p) (r : R) : Homogeneous n (r • p) := by
  intro w hw
  simp [hp w hw]

theorem homogeneous_word (w : List ι) : Homogeneous w.length (word (R := R) w) := by
  classical
  intro v hv
  rw [wordCoefficients_word]
  have hne : FreeMonoid.ofList w ≠ v := by
    intro h
    subst v
    exact hv rfl
  simp [Ne.symm hne]

theorem Homogeneous.sum {κ : Type*} {n : ℕ} (s : Finset κ)
    (f : κ → FreeAlgebra R ι) (hf : ∀ i ∈ s, Homogeneous n (f i)) :
    Homogeneous n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Homogeneous.zero (R := R) (ι := ι) n
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Associative multiplication adds ordinary word degrees. -/
theorem Homogeneous.mul {n m : ℕ} {p q : FreeAlgebra R ι}
    (hp : Homogeneous n p) (hq : Homogeneous m q) : Homogeneous (n + m) (p * q) := by
  classical
  conv_rhs => rw [← sum_wordCoefficients p, ← sum_wordCoefficients q]
  simp only [Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
  apply Homogeneous.sum
  intro v hv
  apply Homogeneous.sum
  intro w hw
  rw [smul_mul_smul, ← word_append]
  have hl : (w.toList ++ v.toList).length = n + m := by
    rw [List.length_append, homogeneous_iff_support.mp hp w hw,
      homogeneous_iff_support.mp hq v hv]
  exact (hl ▸ homogeneous_word (R := R) (w.toList ++ v.toList)).smul _

/-- The Euler derivation acts by the usual word degree on homogeneous
associative polynomials; no Lie-membership assumption is needed here. -/
theorem euler_eq_degree_smul {n : ℕ} {p : FreeAlgebra R ι}
    (hp : Homogeneous n p) : euler p = (n : R) • p := by
  classical
  have hsupport := homogeneous_iff_support.mp hp
  calc
    euler p = euler ((wordCoefficients p).sum
        (fun w r => r • word (R := R) w.toList)) := by rw [sum_wordCoefficients]
    _ = ∑ w ∈ (wordCoefficients p).support,
        wordCoefficients p w • euler (word (R := R) w.toList) := by
      simp only [Finsupp.sum, map_sum, map_smul]
    _ = ∑ w ∈ (wordCoefficients p).support,
        (n : R) • (wordCoefficients p w • word (R := R) w.toList) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [euler_word, hsupport w hw]
      exact smul_comm _ _ _
    _ = (n : R) • p := by
      rw [← Finset.smul_sum]
      exact congrArg (fun q : FreeAlgebra R ι => (n : R) • q) (sum_wordCoefficients p)

/-- Classical DSW with the usual two separate assumptions: Lie membership and
homogeneous associative word support. -/
theorem dynkin_eq_degree_smul_of_isLie {n : ℕ} {p : FreeAlgebra R ι}
    (hp : IsLie p) (hn : Homogeneous n p) : dynkin p = (n : R) • p := by
  rw [dynkin_eq_euler_of_isLie hp, euler_eq_degree_smul hn]

/-- The normalized right Dynkin projection fixes homogeneous Lie polynomials. -/
theorem inv_degree_smul_dynkin_of_isLie {K : Type*} [Field K] {n : ℕ}
    {p : FreeAlgebra K ι} (hn : (n : K) ≠ 0) (hp : IsLie p)
    (hhom : Homogeneous n p) : (n : K)⁻¹ • dynkin p = p := by
  rw [dynkin_eq_degree_smul_of_isLie hp hhom, smul_smul, inv_mul_cancel₀ hn, one_smul]

end

end AltOMD.DynkinProjection
