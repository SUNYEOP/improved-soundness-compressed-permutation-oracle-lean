import QuantumOracle.Proof.SpechtOrthogonal

/-!
# The actual knowledge filtration in the full Specht decomposition

All copies of a Specht type have the same proved Gram scalar. The full Hilbert
projections commute with Gram, preserve the actual knowledge and harmonic
spaces, and characterize arbitrary vectors by which projected blocks vanish.
The conditions use the computed Gram eigenvalues, without assuming a first-row
formula or a spectral decomposition.
-/

noncomputable section

namespace QuantumOracle.SpechtIsotypicLayers

open PermutationExtensions SpechtIsotypic SpechtCharacter KnowledgeSpace HarmonicLayers
open scoped InnerProductSpace BigOperators

theorem exists_ne_zero (N : ℕ) (la : Nat.Partition N) :
    ∃ h ∈ space N la, h ≠ 0 := by
  obtain ⟨h, hh, hn⟩ := SpechtLayers.exists_ne_zero N la
  exact ⟨h, spechtSpace_le_space N la hh, hn⟩

theorem mem_orthogonal_iff {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ (K N t)ᗮ ↔ eigenvalue N t la = 0 := by
  rw [← GramFiltration.ker_gram, LinearMap.mem_ker, gram_eq_eigenvalue N t la hh]
  exact smul_eq_zero.trans (or_iff_left hne)

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

theorem mem_H_succ_iff {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0) :
    h ∈ H N (t + 1) ↔ eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0 := by
  rw [H_succ, Submodule.mem_inf, mem_K_iff hh hne, mem_orthogonal_iff hh hne]

theorem space_le_K_iff (N t : ℕ) (la : Nat.Partition N) :
    space N la ≤ K N t ↔ eigenvalue N t la ≠ 0 := by
  constructor
  · intro hs
    obtain ⟨h, hh, hn⟩ := exists_ne_zero N la
    exact (mem_K_iff hh hn).mp (hs hh)
  · intro he h hh
    by_cases hz : h = 0
    · simpa only [hz] using (K N t).zero_mem
    · exact (mem_K_iff hh hz).mpr he

theorem space_le_orthogonal_iff (N t : ℕ) (la : Nat.Partition N) :
    space N la ≤ (K N t)ᗮ ↔ eigenvalue N t la = 0 := by
  constructor
  · intro hs
    obtain ⟨h, hh, hn⟩ := exists_ne_zero N la
    exact (mem_orthogonal_iff hh hn).mp (hs hh)
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

theorem eigenvalue_re_pos_of_mem_K {N t : ℕ} {la : Nat.Partition N}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) (hne : h ≠ 0)
    (hk : h ∈ K N t) : 0 < (eigenvalue N t la).re :=
  (SpechtLayers.eigenvalue_re_pos_iff N t la).mpr ((mem_K_iff hh hne).mp hk)

/-- The actual orthogonal block projection commutes with every actual Gram map. -/
theorem projection_gram (N t : ℕ) (la : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm N)) :
    (space N la).starProjection (GramFiltration.gram N t h) =
      GramFiltration.gram N t ((space N la).starProjection h) := by
  apply (GramConvolution.equiv N).injective
  have he := (SpechtOrthogonal.projectionAlgebra N la).map_smul
    (GramConvolution.kernel N t) (GramConvolution.equiv N h)
  change GramConvolution.equiv N ((space N la).starProjection
      ((GramConvolution.equiv N).symm
        (GramConvolution.kernel N t * GramConvolution.equiv N h))) =
    GramConvolution.kernel N t * GramConvolution.equiv N ((space N la).starProjection
      ((GramConvolution.equiv N).symm (GramConvolution.equiv N h))) at he
  rw [← GramConvolution.equiv_gram_left] at he
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [GramConvolution.equiv_gram_left]
  exact he

theorem projection_mem_K {N t : ℕ} (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ K N t) :
    (space N la).starProjection h ∈ K N t := by
  rw [← GramFiltration.range_gram] at hh
  obtain ⟨v, rfl⟩ := hh
  rw [projection_gram]
  exact GramFiltration.gram_mem N t _

theorem projection_mem_orthogonal {N t : ℕ} (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ (K N t)ᗮ) :
    (space N la).starProjection h ∈ (K N t)ᗮ := by
  rw [← GramFiltration.ker_gram, LinearMap.mem_ker] at hh ⊢
  rw [← projection_gram, hh, map_zero]

theorem projection_mem_H {N t : ℕ} (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    (space N la).starProjection h ∈ H N t := by
  cases t with
  | zero => exact projection_mem_K la hh
  | succ t => exact ⟨projection_mem_K la hh.1, projection_mem_orthogonal la hh.2⟩

/-- A vector lies in the actual knowledge space exactly when its zero-eigenvalue
blocks vanish. This applies to arbitrary vectors, including the zero vector. -/
theorem mem_K_iff_projection_eq_zero (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ K N t ↔ ∀ la : Nat.Partition N,
      eigenvalue N t la = 0 → (space N la).starProjection h = 0 := by
  constructor
  · intro hh la he
    have hp := projection_mem_K la hh
    have ho := (space_le_orthogonal_iff N t la).mpr he
      ((space N la).starProjection_apply_mem h)
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (ho _ hp)
  · intro hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases he : eigenvalue N t la = 0
    · rw [hh la he]
      exact (K N t).zero_mem
    · exact (space_le_K_iff N t la).mpr he ((space N la).starProjection_apply_mem h)

/-- The actual orthogonal complement consists of the zero-eigenvalue blocks. -/
theorem mem_orthogonal_iff_projection_eq_zero (N t : ℕ)
    (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ (K N t)ᗮ ↔ ∀ la : Nat.Partition N,
      eigenvalue N t la ≠ 0 → (space N la).starProjection h = 0 := by
  constructor
  · intro hh la he
    have hp := projection_mem_orthogonal la hh
    have hk := (space_le_K_iff N t la).mpr he
      ((space N la).starProjection_apply_mem h)
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hp _ hk)
  · intro hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases he : eigenvalue N t la = 0
    · exact (space_le_orthogonal_iff N t la).mpr he
        ((space N la).starProjection_apply_mem h)
    · rw [hh la he]
      exact ((K N t)ᗮ).zero_mem

theorem mem_H_zero_iff_projection_eq_zero (N : ℕ)
    (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ H N 0 ↔ ∀ la : Nat.Partition N,
      eigenvalue N 0 la = 0 → (space N la).starProjection h = 0 :=
  mem_K_iff_projection_eq_zero N 0 h

/-- An arbitrary vector is in a harmonic increment exactly when every nonzero
full isotypic projection first becomes supported at that increment. -/
theorem mem_H_succ_iff_projection_support (N t : ℕ)
    (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ H N (t + 1) ↔ ∀ la : Nat.Partition N,
      (space N la).starProjection h ≠ 0 →
        eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0 := by
  constructor
  · intro hh la hn
    exact (mem_H_succ_iff ((space N la).starProjection_apply_mem h) hn).mp
      (projection_mem_H la hh)
  · intro hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases hz : (space N la).starProjection h = 0
    · rw [hz]
      exact (H N (t + 1)).zero_mem
    · exact (mem_H_succ_iff ((space N la).starProjection_apply_mem h) hz).mpr (hh la hz)

/-- The actual knowledge space is exactly the sum of full nonzero-eigenvalue blocks. -/
theorem K_eq_iSup (N t : ℕ) :
    K N t = ⨆ la : {la : Nat.Partition N // eigenvalue N t la ≠ 0}, space N la.val := by
  apply le_antisymm
  · intro h hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases he : eigenvalue N t la = 0
    · rw [(mem_K_iff_projection_eq_zero N t h).mp hh la he]
      exact Submodule.zero_mem _
    · exact (le_iSup (fun la : {la : Nat.Partition N // eigenvalue N t la ≠ 0} =>
        space N la.val) ⟨la, he⟩) ((space N la).starProjection_apply_mem h)
  · exact iSup_le fun la => (space_le_K_iff N t la.val).mpr la.property

/-- The actual harmonic increment is exactly the sum of blocks first supported there. -/
theorem H_succ_eq_iSup (N t : ℕ) :
    H N (t + 1) = ⨆ la : {la : Nat.Partition N //
      eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0}, space N la.val := by
  apply le_antisymm
  · intro h hh
    rw [← SpechtOrthogonal.sum_projection N h]
    apply Submodule.sum_mem
    intro la _
    by_cases hz : (space N la).starProjection h = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · have he := (mem_H_succ_iff_projection_support N t h).mp hh la hz
      exact (le_iSup (fun la : {la : Nat.Partition N //
        eigenvalue N (t + 1) la ≠ 0 ∧ eigenvalue N t la = 0} => space N la.val)
        ⟨la, he⟩) ((space N la).starProjection_apply_mem h)
  · exact iSup_le fun la => (space_le_H_succ_iff N t la.val).mpr la.property

/-- Parseval's identity for all actual full Specht isotypic projections. -/
theorem norm_sq_eq_sum_projections (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    ‖h‖ ^ 2 = ∑ la : Nat.Partition N, ‖(space N la).starProjection h‖ ^ 2 := by
  calc
    ‖h‖ ^ 2 = RCLike.re ⟪h, h⟫_ℂ := norm_sq_eq_re_inner h
    _ = RCLike.re ⟪∑ la : Nat.Partition N, (space N la).starProjection h, h⟫_ℂ := by
      rw [SpechtOrthogonal.sum_projection]
    _ = ∑ la : Nat.Partition N, RCLike.re ⟪(space N la).starProjection h, h⟫_ℂ := by
      rw [sum_inner, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro la _
      exact (space N la).re_inner_starProjection_eq_normSq h

end QuantumOracle.SpechtIsotypicLayers
