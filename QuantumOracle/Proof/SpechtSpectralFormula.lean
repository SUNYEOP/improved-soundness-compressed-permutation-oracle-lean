import QuantumOracle.Proof.SpechtMinimalMultiplicity
import QuantumOracle.Proof.SpechtIsotypicLayers

/-!
# Actual full Specht blocks at their manuscript harmonic degree

The first-row support and minimal hook scalar are attached here to the full
regular isotypic blocks, including every multiplicity. No Gram eigenvector or
harmonic-degree hypothesis is supplied by the caller.
-/

noncomputable section

namespace QuantumOracle.SpechtSpectralFormula

open PermutationExtensions SpechtFoundation HookRowFactorization
open SpechtCharacter KnowledgeSpace HarmonicLayers
open scoped BigOperators

theorem space_le_K_iff_rowLen (N t : ℕ) (ht : t ≤ N) (la : Nat.Partition N) :
    SpechtIsotypic.space N la ≤ K N t ↔ N - t ≤ (diagram la).rowLen 0 := by
  rw [SpechtIsotypicLayers.space_le_K_iff,
    SpechtMinimalMultiplicity.eigenvalue_ne_zero_iff_rowLen N t ht la]

theorem space_le_H_minimal (N : ℕ) (la : Nat.Partition N) :
    SpechtIsotypic.space N la ≤ H N (tail (diagram la)).card := by
  have he := SpechtMinimalMultiplicity.eigenvalue_minimal_ne_zero N la
  cases ht : (tail (diagram la)).card with
  | zero =>
    apply (SpechtIsotypicLayers.space_le_H_zero_iff N la).mpr
    simpa only [ht] using he
  | succ t =>
    apply (SpechtIsotypicLayers.space_le_H_succ_iff N t la).mpr
    refine ⟨by simpa only [ht] using he, ?_⟩
    have hr := SpechtMinimalMultiplicity.rowLen_add_tail_card N la
    apply SpechtMultiplicitySupport.eigenvalue_eq_zero_of_rowLen_lt N t (by omega) la
    omega

/-- The actual Gram equation on every copy of this Specht type, with its
explicit normalized first-row hook product and its proved harmonic degree. -/
theorem gram_minimal (N : ℕ) (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ SpechtIsotypic.space N la) :
    GramFiltration.gram N (tail (diagram la)).card h =
      (HookRatioProducts.normalizedRowProduct ((diagram la).rowLen 0)
        (tail (diagram la)) : ℂ) • h := by
  rw [SpechtIsotypic.gram_eq_eigenvalue N _ la hh,
    SpechtMinimalMultiplicity.eigenvalue_minimal]

/-- A full Specht type belongs to exactly the layer indexed by its tail size. -/
theorem space_le_H_iff_tail_card (N t : ℕ) (la : Nat.Partition N) :
    SpechtIsotypic.space N la ≤ H N t ↔ (tail (diagram la)).card = t := by
  by_cases ht : t ≤ N
  · have hr := SpechtMinimalMultiplicity.rowLen_add_tail_card N la
    cases t with
    | zero =>
      rw [SpechtIsotypicLayers.space_le_H_zero_iff,
        SpechtMinimalMultiplicity.eigenvalue_ne_zero_iff_rowLen N 0 (by omega) la]
      omega
    | succ t =>
      have he : eigenvalue N t la = 0 ↔ (diagram la).rowLen 0 < N - t := by
        simpa only [not_not, not_le] using not_congr
          (SpechtMinimalMultiplicity.eigenvalue_ne_zero_iff_rowLen N t (by omega) la)
      rw [SpechtIsotypicLayers.space_le_H_succ_iff,
        SpechtMinimalMultiplicity.eigenvalue_ne_zero_iff_rowLen N (t + 1) ht la, he]
      omega
  · have hgt : N < t := Nat.lt_of_not_ge ht
    have htail := SpechtMinimalMultiplicity.tail_card_le N la
    constructor
    · intro hs
      obtain ⟨h, hh, hn⟩ := SpechtIsotypicLayers.exists_ne_zero N la
      have hz := hs hh
      rw [H_eq_bot_of_gt hgt] at hz
      exact (hn hz).elim
    · intro he
      omega

/-- Any vector in a nonmatching actual block is perpendicular to the requested layer. -/
theorem space_le_H_orthogonal_of_tail_ne {N t : ℕ} (la : Nat.Partition N)
    (hne : (tail (diagram la)).card ≠ t) :
    SpechtIsotypic.space N la ≤ (H N t)ᗮ := by
  by_cases ht : t ≤ N
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (space_le_H_minimal N la).trans
        (Submodule.IsOrtho.symm (HarmonicLayers.orthogonal_of_lt hlt ht))
    · exact (space_le_H_minimal N la).trans
        (HarmonicLayers.orthogonal_of_lt hgt (SpechtMinimalMultiplicity.tail_card_le N la))
  · rw [H_eq_bot_of_gt (Nat.lt_of_not_ge ht), Submodule.bot_orthogonal_eq_top]
    exact le_top

/-- An arbitrary vector is in `H_t` precisely when every full block of a
different tail size vanishes under its actual orthogonal projection. -/
theorem mem_H_iff_projection_eq_zero (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ H N t ↔ ∀ la : Nat.Partition N, (tail (diagram la)).card ≠ t →
      (SpechtIsotypic.space N la).starProjection h = 0 := by
  constructor
  · intro hh la hne
    have hp := SpechtIsotypicLayers.projection_mem_H la hh
    have ho := space_le_H_orthogonal_of_tail_ne la hne
      ((SpechtIsotypic.space N la).starProjection_apply_mem h)
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (ho _ hp)
  · intro hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases he : (tail (diagram la)).card = t
    · exact (space_le_H_iff_tail_card N t la).mpr he
        ((SpechtIsotypic.space N la).starProjection_apply_mem h)
    · rw [hh la he]
      exact (H N t).zero_mem

end QuantumOracle.SpechtSpectralFormula
