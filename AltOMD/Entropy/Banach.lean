import AltOMD.Entropy.BanachCompact
import AltOMD.Entropy.BanachDiagonal

/-! Banach's diagonal-norm equality for symmetric forms on finite-dimensional
real Hilbert spaces. Compactness is expressed by the `ProperSpace` assumption. -/

open scoped BigOperators

namespace AltOMD.Polarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- A symmetric multilinear form on a nontrivial finite-dimensional real
Hilbert space attains its norm at a constant unit tuple. -/
theorem exists_diagonal_norm_eq [Nontrivial E] {n : ℕ} (hn : 1 ≤ n)
    (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v) :
    ∃ h : E, ‖h‖ = 1 ∧ |M (fun _ => h)| = ‖M‖ := by
  obtain ⟨v, hv, hMv, hmax⟩ := exists_norm_sum_maximizer M
  have hconst := norm_sum_maximizer_is_constant M hM v hv hMv hmax
  let i : Fin n := ⟨0, hn⟩
  refine ⟨v i, hv i, ?_⟩
  have heq : (fun _ : Fin n => v i) = v := funext fun j => hconst i j
  simpa only [heq] using hMv

/-- Banach's theorem: for a symmetric multilinear form on a finite-dimensional
real Hilbert space, the full operator norm equals the supremum of its absolute
diagonal values on the closed unit ball. This includes the zero-dimensional space. -/
theorem norm_eq_diagonal_sup {n : ℕ} (hn : 1 ≤ n) (M : E [×n]→L[ℝ] ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), M (v ∘ σ) = M v) :
    ‖M‖ = sSup ((fun h : E => |M (fun _ => h)|) '' Metric.closedBall 0 1) := by
  have hbound (h : E) (hh : h ∈ Metric.closedBall (0 : E) 1) :
      |M (fun _ => h)| ≤ ‖M‖ := by
    apply M.unit_le_opNorm
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro _
    simpa using hh
  have hb : BddAbove ((fun h : E => |M (fun _ => h)|) '' Metric.closedBall 0 1) := by
    refine ⟨‖M‖, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact hbound h hh
  have hne : ((fun h : E => |M (fun _ => h)|) '' Metric.closedBall 0 1).Nonempty :=
    ⟨_, 0, by simp, rfl⟩
  apply le_antisymm
  · cases subsingleton_or_nontrivial E with
    | inl hE =>
      let := hE
      have hzero : M = 0 := by
        ext v
        exact M.map_coord_zero ⟨0, hn⟩ (Subsingleton.elim _ _)
      have hnonneg := (abs_nonneg (M (fun _ => (0 : E)))).trans
        (le_csSup hb ⟨0, by simp, rfl⟩)
      simpa only [hzero, norm_zero] using hnonneg
    | inr hE =>
      let := hE
      obtain ⟨h, hh, heq⟩ := exists_diagonal_norm_eq hn M hM
      rw [← heq]
      exact le_csSup hb ⟨h, by simpa using hh.le, rfl⟩
  · apply csSup_le hne
    rintro _ ⟨h, hh, rfl⟩
    exact hbound h hh

end AltOMD.Polarization
