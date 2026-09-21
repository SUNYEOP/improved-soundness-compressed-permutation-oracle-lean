import QuantumOracle.Proof.ResidualKnowledge
import QuantumOracle.Proof.PolarOrthogonal
import QuantumOracle.Proof.ConditioningInverse

/-!
# Actual degree support of residual conditioning

Restriction lowers the knowledge filtration and transfers orthogonality through
its adjoint. Together with the proved polar degree correspondence and actual
edge insertion, this forces conditioning of degree t to have database sizes
t or t+1. No irreducible decomposition or spectral formula is assumed.
-/

noncomputable section

namespace QuantumOracle.ConditioningDegree

open PermutationExtensions HarmonicLayers

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K

/-- A cumulative knowledge bound grows by at most one under actual conditioning. -/
theorem J_apply_eq_zero_of_mem_K {N t : ℕ} (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ KnowledgeSpace.K (N + 1) t)
    (I : Database (N + 1)) (hI : t + 1 < I.size) : Conditioning.J x h I = 0 := by
  classical
  by_cases hmem : I ∈ Set.range (ResidualDatabase.jointInsert x)
  · obtain ⟨⟨y, R⟩, rfl⟩ := hmem
    change Conditioning.J x h (ResidualDatabase.insert x y R) = 0
    rw [Conditioning.J_apply_insert]
    change PolarEmbedding.candidate N (ResidualAdjoint.restrict x y h) R = 0
    apply PolarDegree.candidate_apply_eq_zero_of_mem_K
      (ResidualKnowledge.restrict_mem_K x y hh)
    have hs : (ResidualDatabase.jointInsert x (y, R)).size = R.size + 1 :=
      ResidualDatabase.insert_size x y R
    have hm := Nat.min_le_left t N
    omega
  · exact Conditioning.J_apply_of_notMem x h I hmem

/-- Lower knowledge orthogonality rules out every output size below the input degree. -/
theorem J_apply_eq_zero_of_low_size {N t : ℕ} (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (I : Database (N + 1)) (hI : I.size < t) : Conditioning.J x h I = 0 := by
  classical
  by_cases ht : t ≤ N + 1
  · by_cases hmem : I ∈ Set.range (ResidualDatabase.jointInsert x)
    · obtain ⟨⟨y, R⟩, rfl⟩ := hmem
      have hs : (ResidualDatabase.jointInsert x (y, R)).size = R.size + 1 :=
        ResidualDatabase.insert_size x y R
      change Conditioning.J x h (ResidualDatabase.insert x y R) = 0
      rw [Conditioning.J_apply_insert]
      change PolarEmbedding.candidate N (ResidualAdjoint.restrict x y h) R = 0
      apply PolarOrthogonal.candidate_apply_eq_zero_of_orthogonal_size
      apply ResidualAdjoint.restrict_mem_orthogonal
      cases t with
      | zero => omega
      | succ s =>
        exact Submodule.orthogonal_le
          (KnowledgeSpace.mono (s := R.size + 1) (t := s) (by omega) (by omega))
          (H_succ_le_orthogonal (N + 1) s hh)
    · exact Conditioning.J_apply_of_notMem x h I hmem
  · have hz : h = 0 := by
      simpa only [H_eq_bot_of_gt (Nat.lt_of_not_ge ht), Submodule.mem_bot] using hh
    rw [hz, map_zero]
    rfl

/-- The actual J image of a pure degree has precisely the two permitted size levels. -/
theorem J_supported_two_levels {N t : ℕ} (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (I : Database (N + 1)) (hI : I.size ≠ t) (hI' : I.size ≠ t + 1) :
    Conditioning.J x h I = 0 := by
  by_cases hlow : I.size < t
  · exact J_apply_eq_zero_of_low_size x hh I hlow
  · exact J_apply_eq_zero_of_mem_K x (H_le_K (N + 1) t hh) I (by omega)

/-- The same physical two-level assertion holds in the inverse query direction. -/
theorem JInverse_supported_two_levels {N t : ℕ} (x : Fin (N + 1))
    {h : EuclideanSpace ℂ (Perm (N + 1))} (hh : h ∈ H (N + 1) t)
    (I : Database (N + 1)) (hI : I.size ≠ t) (hI' : I.size ≠ t + 1) :
    ConditioningInverse.JInverse x h I = 0 := by
  rw [ConditioningInverse.JInverse_apply]
  exact J_supported_two_levels x (InversionSymmetry.oracle_mem_H h hh) I.inverse
    (by simpa only [Database.inverse_size] using hI)
    (by simpa only [Database.inverse_size] using hI')

/-- On its actual image domain, D sends a physical degree t only to t and t+1. -/
theorem D_supported_two_levels {N t : ℕ} (x : Fin (N + 1))
    (ψ : Conditioning.Image (N + 1)) (hψ : ψ.val ∈ DatabaseDegree.exactLevel (N + 1) t)
    (I : Database (N + 1)) (hI : I.size ≠ t) (hI' : I.size ≠ t + 1) :
    Conditioning.D x ψ I = 0 := by
  rcases ψ with ⟨_, ⟨h, rfl⟩⟩
  have hh : h ∈ H (N + 1) t := (PolarOrthogonal.candidate_mem_exactLevel_iff h).mp hψ
  change Conditioning.D x ((PolarEmbedding.candidate (N + 1)).equivRange h) I = 0
  rw [Conditioning.D_candidate]
  exact J_supported_two_levels x hh I hI hI'

end QuantumOracle.ConditioningDegree
