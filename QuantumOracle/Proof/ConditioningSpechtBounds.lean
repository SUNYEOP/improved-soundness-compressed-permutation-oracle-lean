import QuantumOracle.Proof.ConditioningHookBounds
import QuantumOracle.Proof.SpechtSpectralFormula
import QuantumOracle.Proof.YoungBranchCases
import QuantumOracle.Proof.JointSpectralDecomposition

/-!
# Actual conditioning bound on an allowed joint Specht branch

Membership in actual full and residual isotypic blocks supplies both harmonic
degrees and both computed hook-product Gram equations internally. The only
branching premise is that the actual residual partition is obtained by corner
deletion. Establishing support on such pairs, and combining their error images
orthogonally, remain separate obligations for the uniform knowledge-space bound.
-/

noncomputable section

namespace QuantumOracle.ConditioningSpechtBounds

open PermutationExtensions SpechtFoundation HookRowFactorization
open AtlasKnownTheorems.HookLengthFormula

attribute [local irreducible] PolarEmbedding.candidate

variable {N : ℕ}

/-- The manuscript constant for actual full/residual types in either allowed
corner branch, without any supplied degree or Gram eigenvalue equations. -/
theorem error_le (x : Fin (N + 1)) (la : Nat.Partition (N + 1)) (mu : Nat.Partition N)
    (hbranch : mu ∈ removeCorners la) (hsparse : 4 * (tail (diagram la)).card ≤ N + 1)
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ SpechtIsotypic.space (N + 1) la)
    (hres : ∀ y, ResidualAdjoint.restrict x y h ∈ SpechtIsotypic.space N mu) :
    ‖Conditioning.J x h - Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤
      (2 / Real.sqrt (N + 1 : ℕ)) * ‖h‖ := by
  have hdegree := SpechtSpectralFormula.space_le_H_minimal (N + 1) la hh
  have hresdegree := fun y => SpechtSpectralFormula.space_le_H_minimal N mu (hres y)
  have hfull := SpechtSpectralFormula.gram_minimal (N + 1) la hh
  have hresgram := fun y => SpechtSpectralFormula.gram_minimal N mu (hres y)
  have hcard := SpechtMinimalMultiplicity.rowLen_add_tail_card (N + 1) la
  have hr : (diagram la).rowLen 0 = N + 1 - (tail (diagram la)).card := by omega
  rw [hr] at hfull
  rcases YoungBranchCases.branching_cases la mu hbranch with ⟨hrow, htail⟩ | ⟨hrow, c, htail⟩
  · have hm : (diagram mu).rowLen 0 = N + 1 - (tail (diagram la)).card - 1 := by omega
    simp only [htail] at hresdegree
    simp only [htail, hm] at hresgram
    exact ConditioningHookBounds.firstRow_error_le x (tail (diagram la)) hsparse
      hdegree hresdegree hfull hresgram
  · simp only [htail] at hresdegree
    simp only [htail, hrow, hr] at hresgram
    exact ConditioningHookBounds.tailCorner_error_le x (tail (diagram la)) c hsparse
      hdegree hresdegree hfull hresgram

/-- Apply the bound to the constructed actual joint projection. Allowed-branch
support remains visible as a partition-containment premise. -/
theorem error_project_le (x : Fin (N + 1)) (la : Nat.Partition (N + 1))
    (mu : Nat.Partition N) (hbranch : mu ∈ removeCorners la)
    (hsparse : 4 * (tail (diagram la)).card ≤ N + 1)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ‖Conditioning.J x (JointSpectralDecomposition.project x (la, mu) h) -
        Compression.pC x (PolarEmbedding.candidate (N + 1)
          (JointSpectralDecomposition.project x (la, mu) h))‖ ≤
      (2 / Real.sqrt (N + 1 : ℕ)) * ‖JointSpectralDecomposition.project x (la, mu) h‖ := by
  have hp := JointSpectralDecomposition.project_mem x (la, mu) h
  exact error_le x la mu hbranch hsparse hp.1
    ((ResidualSpectralDecomposition.mem_space x mu _).mp hp.2)

end QuantumOracle.ConditioningSpechtBounds
