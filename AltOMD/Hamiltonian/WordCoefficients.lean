import AltOMD.Hamiltonian.Coefficients
import AltOMD.Hamiltonian.FormalEnergy
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.Ring

/-!
# Explicit word expansions and their coefficient mass

Words are lists in two letters. A polynomial representation is a list of
coefficient/word pairs; repeated words need not be collected. Its mass is thus
an upper bound on the usual ℓ¹ coefficient norm. This representation is useful
because multiplying polynomials preserves mass exactly before collection.
-/

namespace AltOMD
namespace WordCoefficients

open scoped BigOperators

noncomputable section

abbrev Word := List Bool
abbrev Polynomial := List (ℝ × Word)

def mass : Polynomial → ℝ
  | [] => 0
  | (c, _) :: p => |c| + mass p

theorem mass_nonneg (p : Polynomial) : 0 ≤ mass p := by
  induction p with
  | nil => simp [mass]
  | cons t p hp => exact add_nonneg (abs_nonneg _) hp

@[simp] theorem mass_append (p q : Polynomial) : mass (p ++ q) = mass p + mass q := by
  induction p with
  | nil => simp [mass]
  | cons t p hp => simp [mass, hp, add_assoc]

def scale (c : ℝ) (p : Polynomial) : Polynomial := p.map fun t => (c * t.1, t.2)

@[simp] theorem mass_scale (c : ℝ) (p : Polynomial) : mass (scale c p) = |c| * mass p := by
  induction p with
  | nil => simp [scale, mass]
  | cons t p hp =>
    change |c * t.1| + mass (scale c p) = |c| * (|t.1| + mass p)
    rw [hp, abs_mul, mul_add]

def prepend (c : ℝ) (w : Word) (p : Polynomial) : Polynomial :=
  p.map fun t => (c * t.1, w ++ t.2)

@[simp] theorem mass_prefix (c : ℝ) (w : Word) (p : Polynomial) :
    mass (prepend c w p) = |c| * mass p := by
  induction p with
  | nil => simp [prepend, mass]
  | cons t p hp =>
    change |c * t.1| + mass (prepend c w p) = |c| * (|t.1| + mass p)
    rw [hp, abs_mul, mul_add]

def mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | (c, w) :: p, q => prepend c w q ++ mul p q

@[simp] theorem mass_mul (p q : Polynomial) : mass (mul p q) = mass p * mass q := by
  induction p with
  | nil => simp [mul, mass]
  | cons t p hp => simp [mul, mass, hp, add_mul]

def one : Polynomial := [(1, [])]

def product : List Polynomial → Polynomial
  | [] => one
  | p :: ps => mul p (product ps)

theorem mass_flatMap {ι : Type*} (s : List ι) (f : ι → Polynomial) :
    mass (s.flatMap f) = (s.map fun i => mass (f i)).sum := by
  induction s with
  | nil => simp [mass]
  | cons i s hs => simp [hs]

theorem mass_map {ι : Type*} (s : List ι) (f : ι → ℝ × Word) :
    mass (s.map f) = (s.map fun i => |(f i).1|).sum := by
  induction s with
  | nil => simp [mass]
  | cons i s hs => simp [mass, hs]

theorem list_sum_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  simpa using (List.sum_toFinset f s.nodup_toList).symm

/-- The uncollected polynomial `E_n = Σ_j U^j V^(n-j)/(j!(n-j)!)`. -/
def exponential (n : ℕ) : Polynomial :=
  (Finset.range (n + 1)).toList.map fun j =>
    (1 / ((j.factorial : ℝ) * ((n - j).factorial : ℝ)),
      List.replicate j true ++ List.replicate (n - j) false)

theorem mass_exponential (n : ℕ) : mass (exponential n) = Coefficients.exponentialMass n := by
  unfold exponential
  rw [mass_map, list_sum_finset]
  apply Finset.sum_congr rfl
  intro j _
  exact abs_of_nonneg (by positivity)

theorem mass_exponential_le (n : ℕ) : mass (exponential n) ≤ (2 : ℝ) ^ n := by
  rw [mass_exponential]
  exact Coefficients.exponentialMass_le n

/-- Every word in a homogeneous representation has the stated length. -/
def Homogeneous (n : ℕ) (p : Polynomial) : Prop :=
  ∀ t ∈ p, t.2.length = n

theorem homogeneous_scale (n : ℕ) (c : ℝ) (p : Polynomial) (hp : Homogeneous n p) :
    Homogeneous n (scale c p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

theorem homogeneous_prefix (n : ℕ) (c : ℝ) (w : Word) (p : Polynomial)
    (hp : Homogeneous n p) : Homogeneous (w.length + n) (prepend c w p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simp [hp u hu]

theorem homogeneous_mul (n m : ℕ) (p q : Polynomial)
    (hp : Homogeneous n p) (hq : Homogeneous m q) : Homogeneous (n + m) (mul p q) := by
  induction p with
  | nil => simp [Homogeneous, mul]
  | cons t p ih =>
    intro u hu
    have ht : t.2.length = n := hp t (by simp)
    have hp' : Homogeneous n p := fun v hv => hp v (by simp [hv])
    rcases List.mem_append.mp hu with hu | hu
    · simpa [ht] using homogeneous_prefix m t.1 t.2 q hq u hu
    · exact ih hp' u hu

theorem exponential_homogeneous (n : ℕ) : Homogeneous n (exponential n) := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  have hjn : j ≤ n := by
    have : j ∈ Finset.range (n + 1) := Finset.mem_toList.mp hj
    exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
  simp [Nat.add_sub_of_le hjn]

theorem exponential_product_homogeneous (blocks : List ℕ) :
    Homogeneous blocks.sum (product (blocks.map exponential)) := by
  induction blocks with
  | nil => simp [Homogeneous, product, one]
  | cons j blocks ih =>
    exact homogeneous_mul j blocks.sum _ _ (exponential_homogeneous j) ih

theorem mass_exponential_product_le (blocks : List ℕ) :
    mass (product (blocks.map exponential)) ≤ (2 : ℝ) ^ blocks.sum := by
  induction blocks with
  | nil => simp [product, one, mass]
  | cons j blocks ih =>
    simp only [List.map_cons, product, mass_mul, List.sum_cons]
    calc
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ blocks.sum :=
        mul_le_mul (mass_exponential_le j) ih (mass_nonneg _) (by positivity)
      _ = _ := (pow_add _ _ _).symm

/-- The finite, explicit word expansion of the degree-`q` logarithm coefficient. -/
noncomputable def logarithm (q : ℕ) : Polynomial :=
  (Finset.univ : Finset (Composition q)).toList.flatMap fun c =>
    scale ((-1 : ℝ) ^ (c.blocks.length + 1) / (c.blocks.length : ℝ))
      (product (c.blocks.map exponential))

theorem logarithm_homogeneous (q : ℕ) : Homogeneous q (logarithm q) := by
  intro t ht
  obtain ⟨c, _hc, hct⟩ := List.mem_flatMap.mp ht
  have hc := homogeneous_scale c.blocks.sum
    ((-1 : ℝ) ^ (c.blocks.length + 1) / (c.blocks.length : ℝ))
    (product (c.blocks.map exponential)) (exponential_product_homogeneous c.blocks)
  simpa using hc t hct

theorem mass_logarithm_le (q : ℕ) : mass (logarithm q) ≤ (4 : ℝ) ^ q := by
  classical
  unfold logarithm
  rw [mass_flatMap, list_sum_finset]
  simp only [mass_scale]
  calc
    _ ≤ ∑ _c : Composition q, (2 : ℝ) ^ q := by
      apply Finset.sum_le_sum
      intro c _
      have hp := mass_exponential_product_le c.blocks
      simp only [c.blocks_sum] at hp
      calc
        _ ≤ 1 * (2 : ℝ) ^ q :=
          mul_le_mul (Coefficients.log_weight_le _) hp (mass_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ q := by simp [composition_card]
    _ ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le q 1))
        (by positivity)
    _ = (4 : ℝ) ^ q := by rw [← mul_pow]; norm_num

/-- The coefficients in Dynkin's BCH formula, before collecting nested
commutators. The index `r` corresponds to degree `q = r + 1`. -/
noncomputable def correctionRepresentation (r : ℕ) : Polynomial :=
  scale (1 / ((r + 1 : ℕ) : ℝ)) (logarithm (r + 1))

theorem correctionRepresentation_homogeneous (r : ℕ) :
    Homogeneous (r + 1) (correctionRepresentation r) :=
  homogeneous_scale _ _ _ (logarithm_homogeneous _)

theorem correctionRepresentation_mass_le (r : ℕ) :
    mass (correctionRepresentation r) ≤ (4 : ℝ) ^ (r + 1) := by
  unfold correctionRepresentation
  rw [mass_scale, abs_of_nonneg (by positivity)]
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact Coefficients.correction_mass_bound r (mass_nonneg _) (mass_logarithm_le _)

variable {A : Type*} [Ring A] [Algebra ℝ A]

def evaluateWord (U V : A) (w : Word) : A :=
  (w.map fun letter => if letter then U else V).prod

def evaluate (U V : A) : Polynomial → A
  | [] => 0
  | (c, w) :: p => c • evaluateWord U V w + evaluate U V p

@[simp] theorem evaluate_append (U V : A) (p q : Polynomial) :
    evaluate U V (p ++ q) = evaluate U V p + evaluate U V q := by
  induction p with
  | nil => simp [evaluate]
  | cons t p hp => simp [evaluate, hp, add_assoc]

@[simp] theorem evaluate_scale (U V : A) (c : ℝ) (p : Polynomial) :
    evaluate U V (scale c p) = c • evaluate U V p := by
  induction p with
  | nil => simp [scale, evaluate]
  | cons t p hp =>
    change (c * t.1) • evaluateWord U V t.2 + evaluate U V (scale c p) =
      c • (t.1 • evaluateWord U V t.2 + evaluate U V p)
    rw [hp, smul_add, mul_smul]

@[simp] theorem evaluate_prefix (U V : A) (c : ℝ) (w : Word) (p : Polynomial) :
    evaluate U V (prepend c w p) = (c • evaluateWord U V w) * evaluate U V p := by
  induction p with
  | nil => simp [prepend, evaluate]
  | cons t p hp =>
    change (c * t.1) • evaluateWord U V (w ++ t.2) + evaluate U V (prepend c w p) =
      (c • evaluateWord U V w) * (t.1 • evaluateWord U V t.2 + evaluate U V p)
    simp [hp, evaluateWord, List.map_append,
      List.prod_append, mul_add, smul_smul, mul_comm c t.1]

@[simp] theorem evaluate_mul (U V : A) (p q : Polynomial) :
    evaluate U V (mul p q) = evaluate U V p * evaluate U V q := by
  induction p with
  | nil => simp [mul, evaluate]
  | cons t p hp => simp [mul, evaluate, hp, add_mul]

section Hamiltonian

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Right-nested brackets in the opposite Poisson Lie algebra. -/
def nestedHamiltonian (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) : Word → E
  | [] => 0
  | [letter] => if letter then G else F
  | letter :: next :: rest =>
    B (nestedHamiltonian B G F (next :: rest)) (if letter then G else F)

def evaluateNested (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) : Polynomial → E
  | [] => 0
  | (c, w) :: p => c • nestedHamiltonian B G F w + evaluateNested B G F p

theorem evaluateNested_eq_sum (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E) (p : Polynomial) :
    evaluateNested B G F p = (p.map fun t => t.1 • nestedHamiltonian B G F t.2).sum := by
  induction p with
  | nil => rfl
  | cons t p hp => simp [evaluateNested, hp]

theorem prefix_prefix (c d : ℝ) (v w : Word) (p : Polynomial) :
    prepend c v (prepend d w p) = prepend (c * d) (v ++ w) p := by
  simp [prepend, List.map_map, Function.comp_def, mul_assoc, List.append_assoc]

theorem homogeneous_nonempty {n : ℕ} {p : Polynomial} (hn : 0 < n)
    (hp : Homogeneous n p) (t : ℝ × Word) (ht : t ∈ p) : t.2 ≠ [] := by
  intro hz
  have := hp t ht
  simp [hz] at this
  omega

theorem nestedHamiltonian_cons (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (letter : Bool) (w : Word) (hw : w ≠ []) :
    nestedHamiltonian B G F (letter :: w) =
      B (nestedHamiltonian B G F w) (if letter then G else F) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons next rest => rfl

theorem evaluateNested_generator (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (letter : Bool) (p : Polynomial) (hp : ∀ t ∈ p, t.2 ≠ []) :
    B.flip (if letter then G else F) (evaluateNested B G F p) =
      evaluateNested B G F (prepend 1 [letter] p) := by
  induction p with
  | nil => simp [evaluateNested, prepend]
  | cons t p ih =>
    have ht : t.2 ≠ [] := hp t (by simp)
    have hp' : ∀ u ∈ p, u.2 ≠ [] := fun u hu => hp u (by simp [hu])
    change B (t.1 • nestedHamiltonian B G F t.2 + evaluateNested B G F p)
      (if letter then G else F) =
        (1 * t.1) • nestedHamiltonian B G F ([letter] ++ t.2) +
          evaluateNested B G F (prepend 1 [letter] p)
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
    rw [show B (evaluateNested B G F p) (if letter then G else F) =
        evaluateNested B G F (prepend 1 [letter] p) from ih hp']
    simp [nestedHamiltonian_cons B G F letter t.2 ht]

theorem evaluateNested_generator_pow (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (letter : Bool) (p : Polynomial) {q : ℕ} (hq : 0 < q) (hp : Homogeneous q p)
    (k : ℕ) :
    ((B.flip (if letter then G else F)) ^ k) (evaluateNested B G F p) =
      evaluateNested B G F (prepend 1 (List.replicate k letter) p) := by
  induction k with
  | zero => simp [prepend]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    have hhom := homogeneous_prefix q 1 (List.replicate k letter) p hp
    rw [evaluateNested_generator B G F letter _
      (homogeneous_nonempty (by simp; omega) hhom)]
    rw [prefix_prefix]
    simp [List.replicate_succ]

/-- Mixed Lie derivatives are represented by prefixing the corresponding letters;
this operation retains coefficient mass and increases every word's length. -/
theorem evaluateNested_mixed_powers (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (G F : E)
    (p : Polynomial) {q : ℕ} (hq : 0 < q) (hp : Homogeneous q p) (α β : ℕ) :
    ((B.flip G) ^ α * (B.flip F) ^ β) (evaluateNested B G F p) =
      evaluateNested B G F
        (prepend 1 (List.replicate α true ++ List.replicate β false) p) := by
  rw [Module.End.mul_apply]
  rw [show ((B.flip F) ^ β) (evaluateNested B G F p) =
      evaluateNested B G F (prepend 1 (List.replicate β false) p) from
    evaluateNested_generator_pow B G F false p hq hp β]
  have hhom := homogeneous_prefix q 1 (List.replicate β false) p hp
  rw [show ((B.flip G) ^ α)
      (evaluateNested B G F (prepend 1 (List.replicate β false) p)) = _ from
    evaluateNested_generator_pow B G F true _ (by simp; omega) hhom α]
  rw [prefix_prefix]
  simp

/-- The Hamiltonian representation supplied by the explicit Dynkin formula in
Proposition A.1. The historical name is retained for compatibility; this is
an application interface, not a separate unproved DSW theorem.
`BCHCoefficients.classicalDSWInput` supplies it for the canonical coefficients.
The Jacobi convention is the usual left-nested cyclic identity. No
quantitative estimate is an input. -/
structure ClassicalDSWInput (Z : ℕ → FormalEnergy.LieExpression) (E : Type*)
    [AddCommGroup E] [Module ℝ E] : Prop where
  representation : ∀ (B : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (_skew : ∀ x y, B x y = -B y x)
    (_jacobi : ∀ x y z, B x (B y z) + B y (B z x) + B z (B x y) = 0)
    (G F : E) (r : ℕ),
    (Z (r + 1)).hamiltonian B G F =
      evaluateNested B G F (correctionRepresentation r)

/-- The actual Hamiltonian coefficient has a right-nested representation with
word length `r+1` and coefficient mass at most `4^(r+1)`. -/
theorem correction_representation_and_bound
    (Z : ℕ → FormalEnergy.LieExpression) (dsw : ClassicalDSWInput Z E)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] E) (hB : ∀ x y, B x y = -B y x)
    (hJacobi : ∀ x y z, B x (B y z) + B y (B z x) + B z (B x y) = 0)
    (G F : E) (r : ℕ) :
    FormalEnergy.correctedHamiltonian B G F Z r =
        evaluateNested B G F (correctionRepresentation r) ∧
      Homogeneous (r + 1) (correctionRepresentation r) ∧
      mass (correctionRepresentation r) ≤ (4 : ℝ) ^ (r + 1) := by
  exact ⟨dsw.representation B hB hJacobi G F r,
    correctionRepresentation_homogeneous r, correctionRepresentation_mass_le r⟩

end Hamiltonian

end
end WordCoefficients
end AltOMD
