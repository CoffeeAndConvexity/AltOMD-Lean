import Mathlib.Algebra.FreeAlgebra
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The right Dynkin map

The right Dynkin map sends an associative word to its right-nested
commutator. This file proves its multiplication identity on Lie polynomials;
`DynkinGrading` proves the degree-scaling identity from ordinary homogeneity.
The coefficient ring is an arbitrary commutative ring, and the alphabet is
arbitrary.

The auxiliary identity `dynkin_mul_of_isLie` explicitly requires its right
factor to have zero constant coefficient: the identity is false on constants.
The proof is a structural version of the right-bracketing argument in
Harald Hofstätter, *A relatively short self-contained proof of the
Baker–Campbell–Hausdorff theorem*, §3, arXiv:2005.00855v2.
-/

namespace AltOMD.DynkinProjection

noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*}

/-- An associative word in the free algebra. -/
def word (w : List ι) : FreeAlgebra R ι := (w.map (FreeAlgebra.ι R)).prod

@[simp] theorem word_nil : word (R := R) ([] : List ι) = 1 := rfl

@[simp] theorem word_cons (i : ι) (w : List ι) :
    word (R := R) (i :: w) = FreeAlgebra.ι R i * word w := rfl

@[simp] theorem word_append (v w : List ι) :
    word (R := R) (v ++ w) = word v * word w := by
  simp [word, List.map_append, List.prod_append]

/-- Right-nested commutators, with the empty word mapped to zero. -/
def nested : List ι → FreeAlgebra R ι
  | [] => 0
  | [i] => FreeAlgebra.ι R i
  | i :: j :: w =>
      FreeAlgebra.ι R i * nested (j :: w) - nested (j :: w) * FreeAlgebra.ι R i

@[simp] theorem nested_nil : nested (R := R) ([] : List ι) = 0 := rfl

@[simp] theorem nested_singleton (i : ι) : nested (R := R) [i] = FreeAlgebra.ι R i := rfl

theorem nested_cons (i : ι) (w : List ι) (hw : w ≠ []) :
    nested (R := R) (i :: w) =
      FreeAlgebra.ι R i * nested w - nested w * FreeAlgebra.ι R i := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons j w => rfl

private abbrev wordEquiv :
    FreeAlgebra R ι ≃ₐ[R] MonoidAlgebra R (FreeMonoid ι) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid

private theorem wordEquiv_word (w : List ι) :
    wordEquiv (word (R := R) w) = MonoidAlgebra.single (FreeMonoid.ofList w) 1 := by
  induction w with
  | nil =>
      change wordEquiv (1 : FreeAlgebra R ι) = 1
      exact map_one _
  | cons i w ih =>
      rw [word_cons, map_mul, ih]
      change (FreeAlgebra.lift R
        (fun x => MonoidAlgebra.of R (FreeMonoid ι) (FreeMonoid.of x)))
          (FreeAlgebra.ι R i) * MonoidAlgebra.single (FreeMonoid.ofList w) 1 = _
      simp only [FreeAlgebra.lift_ι_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_mul_single, one_mul, FreeMonoid.ofList_cons]

/-- The right Dynkin linear map on the free associative algebra. -/
def dynkin : FreeAlgebra R ι →ₗ[R] FreeAlgebra R ι :=
  (Finsupp.lift (FreeAlgebra R ι) R (FreeMonoid ι)
    (fun w => nested (R := R) w.toList)).comp
    ((MonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp wordEquiv.toLinearMap)

@[simp] theorem dynkin_word (w : List ι) :
    dynkin (word (R := R) w) = nested w := by
  change ((MonoidAlgebra.coeffLinearEquiv R) (wordEquiv (word w))).sum
    (fun x r => r • nested x.toList) = nested w
  rw [wordEquiv_word]
  change (Finsupp.single (FreeMonoid.ofList w) (1 : R)).sum
    (fun x r => r • nested x.toList) = nested w
  simp

@[simp] theorem dynkin_one : dynkin (1 : FreeAlgebra R ι) = 0 :=
  dynkin_word []

@[simp] theorem dynkin_generator (i : ι) :
    dynkin (FreeAlgebra.ι R i) = FreeAlgebra.ι R i := by
  simpa using dynkin_word (R := R) [i]

/-- Constant coefficient, equivalently evaluation with every generator zero. -/
abbrev augmentation : FreeAlgebra R ι →ₐ[R] R := FreeAlgebra.algebraMapInv

@[simp] theorem augmentation_generator (i : ι) :
    augmentation (FreeAlgebra.ι R i) = 0 := by
  simp [augmentation, FreeAlgebra.algebraMapInv]

@[simp] theorem augmentation_word_cons (i : ι) (w : List ι) :
    augmentation (word (R := R) (i :: w)) = 0 := by simp

private theorem induction_word (p : FreeAlgebra R ι)
    {P : FreeAlgebra R ι → Prop} (hzero : P 0)
    (hadd : ∀ p q, P p → P q → P (p + q))
    (hword : ∀ (r : R) (w : List ι), P (r • word w)) : P p := by
  obtain ⟨q, rfl⟩ := wordEquiv.symm.surjective p
  induction q using MonoidAlgebra.induction_linear with
  | zero => simpa using hzero
  | add q s hq hs => simpa using hadd _ _ hq hs
  | single w r =>
      have hw : wordEquiv.symm (MonoidAlgebra.single w r) =
          r • word (R := R) w.toList := by
        apply wordEquiv.injective
        simp [wordEquiv_word]
      rw [hw]
      exact hword r w.toList

/-- Prefixing a generator gives a commutator, with the constant correction
included. This version holds for every associative polynomial. -/
theorem dynkin_generator_mul (i : ι) (q : FreeAlgebra R ι) :
    dynkin (FreeAlgebra.ι R i * q) =
      FreeAlgebra.ι R i * dynkin q - dynkin q * FreeAlgebra.ι R i +
        augmentation q • FreeAlgebra.ι R i := by
  induction q using induction_word with
  | hzero => simp
  | hadd p q hp hq => simp only [mul_add, map_add, hp, hq, add_mul, add_smul]; abel
  | hword r w =>
      have hw : dynkin (FreeAlgebra.ι R i * word (R := R) w) =
          FreeAlgebra.ι R i * dynkin (word w) -
            dynkin (word w) * FreeAlgebra.ι R i +
            augmentation (word (R := R) w) • FreeAlgebra.ι R i := by
        cases w with
        | nil => simp
        | cons j w =>
            rw [← word_cons, dynkin_word, dynkin_word, nested_cons _ _ (by simp)]
            simp
      simpa [mul_smul_comm, smul_mul_assoc, smul_sub, smul_add, smul_smul] using
        congrArg (fun p => r • p) hw

/-- The Lie polynomials generated by the alphabet; no scalar constants are
generators of this subspace. -/
inductive IsLie : FreeAlgebra R ι → Prop
  | zero : IsLie 0
  | generator (i : ι) : IsLie (FreeAlgebra.ι R i)
  | add {p q} : IsLie p → IsLie q → IsLie (p + q)
  | smul (r : R) {p} : IsLie p → IsLie (r • p)
  | commutator {p q} : IsLie p → IsLie q → IsLie (p * q - q * p)

theorem IsLie.augmentation_eq_zero {p : FreeAlgebra R ι} (hp : IsLie p) :
    augmentation p = 0 := by
  induction hp with
  | zero => simp
  | generator i => simp
  | add hp hq ihp ihq => simp [ihp, ihq]
  | smul r hp ih => simp [ih]
  | commutator hp hq ihp ihq => simp [ihp, ihq]

/-- The right Dynkin map turns left multiplication by a Lie polynomial into
its adjoint action. The right factor must have zero constant coefficient. -/
theorem dynkin_mul_of_isLie {p : FreeAlgebra R ι} (hp : IsLie p)
    (q : FreeAlgebra R ι) (hq : augmentation q = 0) :
    dynkin (p * q) = p * dynkin q - dynkin q * p := by
  induction hp generalizing q with
  | zero => simp
  | generator i => simp [dynkin_generator_mul, hq]
  | add hp hs ihp ihs =>
      simp only [add_mul, map_add, ihp q hq, ihs q hq, mul_add]
      abel
  | smul r hp ih =>
      simp [ih q hq, smul_sub]
  | @commutator p s hp hs ihp ihs =>
      rw [sub_mul, map_sub, mul_assoc, mul_assoc,
        ihp (s * q) (by simp [hq]), ihs (p * q) (by simp [hq]),
        ihs q hq, ihp q hq]
      noncomm_ring


end

end AltOMD.DynkinProjection
