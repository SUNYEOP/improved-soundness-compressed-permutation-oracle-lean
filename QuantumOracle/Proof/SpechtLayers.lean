import QuantumOracle.Proof.SpechtCharacter
import QuantumOracle.Model.HarmonicLayers

/-!
# Actual knowledge and harmonic layers on constructed Specht spaces

The eigenvalue below is the proved finite character sum for the actual extension
Gram operator. Its vanishing determines the actual kernel, and its nonvanishing
determines the actual range on each constructed Specht space. These statements
do not identify the first row of a partition with a harmonic degree.
-/

noncomputable section

namespace QuantumOracle.SpechtLayers

open PermutationExtensions SpechtGram SpechtCharacter KnowledgeSpace HarmonicLayers
open scoped InnerProductSpace

/-- Every constructed Specht space contains a nonzero actual permutation vector. -/
theorem exists_ne_zero (N : ℕ) (la : Nat.Partition N) :
    ∃ h ∈ space N la, h ≠ 0 := by
  letI := SpechtFoundation.specht_simple N la
  letI := IsSimpleModule.nontrivial (SpechtFoundation.GroupAlgebra N)
    (SpechtFoundation.specht N la)
  obtain ⟨v, hv⟩ := exists_ne (0 : SpechtFoundation.specht N la)
  refine ⟨(GramConvolution.equiv N).symm v.val, ?_, ?_⟩
  · simpa only [mem_space, LinearEquiv.apply_symm_apply] using v.property
  · intro hz
    apply hv
    apply Subtype.ext
    change v.val = 0
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using
      congrArg (GramConvolution.equiv N) hz

/-- Zero vectors are excluded precisely where they cannot determine an eigenvalue. -/
theorem mem_orthogonal_iff {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ (K N t)ᗮ ↔ eigenvalue N t la = 0 := by
  rw [← GramFiltration.ker_gram, LinearMap.mem_ker, gram_eq_eigenvalue N t la hh]
  exact smul_eq_zero.trans (or_iff_left hne)

/-- Nonzero actual Gram eigenvectors belong to its range exactly for nonzero eigenvalues. -/
theorem mem_K_iff {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ K N t ↔ eigenvalue N t la ≠ 0 := by
  constructor
  · intro hk hz
    have ho := (mem_orthogonal_iff hh hne).mpr hz
    exact hne ((inner_self_eq_zero (𝕜 := ℂ)).mp (ho h hk))
  · intro he
    have hm := (K N t).smul_mem (eigenvalue N t la)⁻¹ (GramFiltration.gram_mem N t h)
    simpa only [gram_eq_eigenvalue N t la hh, smul_smul, inv_mul_cancel₀ he,
      one_smul] using hm

theorem mem_H_zero_iff {N : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ H N 0 ↔ eigenvalue N 0 la ≠ 0 :=
  mem_K_iff hh hne

/-- Adjacent actual Gram eigenvalues characterize the actual orthogonal increment. -/
theorem mem_H_succ_iff {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ H N (t + 1) ↔ eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0 := by
  rw [H_succ, Submodule.mem_inf, mem_K_iff hh hne, mem_orthogonal_iff hh hne]

theorem space_le_K_iff (N t : ℕ) (la : Nat.Partition N) :
    space N la ≤ K N t ↔ eigenvalue N t la ≠ 0 := by
  constructor
  · intro hs
    obtain ⟨h, hh, hne⟩ := exists_ne_zero N la
    exact (mem_K_iff hh hne).mp (hs hh)
  · intro he h hh
    by_cases hz : h = 0
    · simpa only [hz] using (K N t).zero_mem
    · exact (mem_K_iff hh hz).mpr he

theorem space_le_orthogonal_iff (N t : ℕ) (la : Nat.Partition N) :
    space N la ≤ (K N t)ᗮ ↔ eigenvalue N t la = 0 := by
  constructor
  · intro hs
    obtain ⟨h, hh, hne⟩ := exists_ne_zero N la
    exact (mem_orthogonal_iff hh hne).mp (hs hh)
  · intro he h hh
    by_cases hz : h = 0
    · simpa only [hz] using ((K N t)ᗮ).zero_mem
    · exact (mem_orthogonal_iff hh hz).mpr he

theorem space_le_H_zero_iff (N : ℕ) (la : Nat.Partition N) :
    space N la ≤ H N 0 ↔ eigenvalue N 0 la ≠ 0 :=
  space_le_K_iff N 0 la

theorem space_le_H_succ_iff (N t : ℕ) (la : Nat.Partition N) :
    space N la ≤ H N (t + 1) ↔
      eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0 := by
  rw [H_succ, le_inf_iff, space_le_K_iff, space_le_orthogonal_iff]

/-- The exact character sum is a real nonnegative Rayleigh quotient of the actual Gram map. -/
theorem eigenvalue_eq_energy_div_norm_sq {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    eigenvalue N t la =
      ((‖(ExtensionOperator.T N t).adjoint h‖ ^ 2 / ‖h‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ((‖h‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  rw [Complex.ofReal_div]
  apply (eq_div_iff hd).mpr
  have he := GramFiltration.inner_gram N t h
  rw [gram_eq_eigenvalue N t la hh, inner_smul_right,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

theorem eigenvalue_im_eq_zero (N t : ℕ) (la : Nat.Partition N) :
    (eigenvalue N t la).im = 0 := by
  obtain ⟨h, hh, hne⟩ := exists_ne_zero N la
  rw [eigenvalue_eq_energy_div_norm_sq hh hne]
  rfl

theorem eigenvalue_re_nonneg (N t : ℕ) (la : Nat.Partition N) :
    0 ≤ (eigenvalue N t la).re := by
  obtain ⟨h, hh, hne⟩ := exists_ne_zero N la
  rw [eigenvalue_eq_energy_div_norm_sq hh hne, Complex.ofReal_re]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem eigenvalue_eq_ofReal_re (N t : ℕ) (la : Nat.Partition N) :
    eigenvalue N t la = ((eigenvalue N t la).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact eigenvalue_im_eq_zero N t la

theorem eigenvalue_re_pos_iff (N t : ℕ) (la : Nat.Partition N) :
    0 < (eigenvalue N t la).re ↔ eigenvalue N t la ≠ 0 := by
  constructor
  · intro hp hz
    rw [hz, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  · intro hn
    have hr : (eigenvalue N t la).re ≠ 0 := by
      intro hz
      apply hn
      rw [eigenvalue_eq_ofReal_re, hz, Complex.ofReal_zero]
    exact lt_of_le_of_ne (eigenvalue_re_nonneg N t la) (Ne.symm hr)

/-- A nonzero vector in the actual knowledge range has a strictly positive real scalar. -/
theorem eigenvalue_re_pos_of_mem_K {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0)
    (hk : h ∈ K N t) : 0 < (eigenvalue N t la).re :=
  (eigenvalue_re_pos_iff N t la).mpr ((mem_K_iff hh hne).mp hk)

/-- Nonvanishing propagates along the valid actual knowledge filtration. -/
theorem eigenvalue_ne_zero_mono {N s t : ℕ} (la : Nat.Partition N)
    (hst : s ≤ t) (ht : t ≤ N) (he : eigenvalue N s la ≠ 0) :
    eigenvalue N t la ≠ 0 := by
  apply (space_le_K_iff N t la).mp
  exact ((space_le_K_iff N s la).mpr he).trans (KnowledgeSpace.mono hst ht)

/-- Outside the available database sizes every constructed Specht eigenvalue is zero. -/
theorem eigenvalue_eq_zero_of_gt {N t : ℕ} (la : Nat.Partition N) (ht : N < t) :
    eigenvalue N t la = 0 := by
  apply (space_le_orthogonal_iff N t la).mp
  rw [KnowledgeSpace.eq_bot_of_gt ht, Submodule.bot_orthogonal_eq_top]
  exact le_top

/-- At the full database level the actual Gram eigenvalue cannot vanish. -/
theorem eigenvalue_full_ne_zero (N : ℕ) (la : Nat.Partition N) :
    eigenvalue N N la ≠ 0 := by
  apply (space_le_K_iff N N la).mp
  rw [KnowledgeSpace.full_eq_top]
  exact le_top

end QuantumOracle.SpechtLayers
