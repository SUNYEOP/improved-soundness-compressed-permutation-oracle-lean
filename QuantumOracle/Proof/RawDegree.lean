import QuantumOracle.Model.RawEmbedding
import QuantumOracle.Proof.HarmonicGram

/-!
# Degree blocks of the actual assembled extension map

The assembled map equals the size-t extension adjoint on the actual harmonic
degree t. Its domain Gram restricts there to the concrete size-t Gram, and
commutes with every degree projection. No scalar spectral formula is assumed.
-/

noncomputable section

namespace QuantumOracle.RawDegree

open PermutationExtensions HarmonicLayers RawHarmonic RawEmbedding GramFiltration
open scoped BigOperators InnerProductSpace

attribute [local irreducible] HarmonicLayers.H KnowledgeSpace.K

theorem projection_eq_zero_of_mem_ne {N s t : ℕ} (hs : s ≤ N) (ht : t ≤ N)
    (hst : s ≠ t) {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    (H N s).starProjection h = 0 := by
  apply (H N s).starProjection_apply_eq_zero_iff.mpr
  rcases lt_or_gt_of_ne hst with hst | hts
  · exact orthogonal_of_lt hst ht hh
  · exact (Submodule.IsOrtho.symm (orthogonal_of_lt hts hs)) hh

theorem total_of_mem_H_of_le {N t : ℕ} (ht : t ≤ N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    total N h = raw N t h := by
  classical
  let i : Fin (N + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
  rw [total_apply]
  calc
    (∑ j : Fin (N + 1), raw N j.val ((H N j.val).starProjection h)) =
        raw N i.val ((H N i.val).starProjection h) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [projection_eq_zero_of_mem_ne (Nat.le_of_lt_succ j.isLt) ht
          (fun heq => hji (Fin.ext heq)) hh, map_zero]
      · simp
    _ = raw N t h := by
      change raw N t ((H N t).starProjection h) = _
      rw [(H N t).starProjection_eq_self_iff.mpr hh]

/-- Every actual degree is sent to its own physical raw database level. -/
theorem total_of_mem_H {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) : total N h = raw N t h := by
  by_cases ht : t ≤ N
  · exact total_of_mem_H_of_le ht hh
  · have hz : h = 0 := by
      simpa only [H_eq_bot_of_gt (Nat.lt_of_not_ge ht), Submodule.mem_bot] using hh
    rw [hz, map_zero, map_zero]

theorem inner_raw_same (N t : ℕ) (h k : EuclideanSpace ℂ (Perm N)) :
    ⟪raw N t h, raw N t k⟫_ℂ = ⟪gram N t h, k⟫_ℂ := by
  change ⟪LevelEmbedding.embed N t ((ExtensionOperator.T N t).adjoint h),
    LevelEmbedding.embed N t ((ExtensionOperator.T N t).adjoint k)⟫_ℂ = _
  rw [(LevelEmbedding.embed N t).inner_map_map,
    (ExtensionOperator.T N t).adjoint_inner_right]
  rfl

theorem total_adjoint_raw {N t : ℕ} (ht : t ≤ N)
    (h : EuclideanSpace ℂ (Perm N)) :
    (total N).adjoint (raw N t h) = (H N t).starProjection (gram N t h) := by
  classical
  apply ext_inner_right ℂ
  intro k
  rw [LinearMap.adjoint_inner_left, total_apply, inner_sum]
  let i : Fin (N + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
  calc
    (∑ j : Fin (N + 1), ⟪raw N t h, raw N j.val ((H N j.val).starProjection k)⟫_ℂ) =
        ⟪raw N t h, raw N i.val ((H N i.val).starProjection k)⟫_ℂ := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact inner_raw_of_ne (fun heq => hji (Fin.ext heq.symm)) _ _
      · simp
    _ = ⟪(H N t).starProjection (gram N t h), k⟫_ℂ := by
      change ⟪raw N t h, raw N t ((H N t).starProjection k)⟫_ℂ = _
      rw [inner_raw_same, ← (H N t).inner_starProjection_left_eq_right]

/-- The actual assembled domain Gram has exactly the size-t Gram on degree t. -/
theorem total_adjoint_total_of_mem_H {N t : ℕ}
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    (total N).adjoint (total N h) = gram N t h := by
  by_cases ht : t ≤ N
  · rw [total_of_mem_H hh, total_adjoint_raw ht,
      (H N t).starProjection_eq_self_iff.mpr (HarmonicGram.gram_mem_H t hh)]
  · have hz : h = 0 := by
      simpa only [H_eq_bot_of_gt (Nat.lt_of_not_ge ht), Submodule.mem_bot] using hh
    rw [hz, map_zero, map_zero, map_zero]

/-- The domain Gram of the actual assembled map. -/
def domainGram (N : ℕ) :
    EuclideanSpace ℂ (Perm N) →ₗ[ℂ] EuclideanSpace ℂ (Perm N) :=
  (total N).adjoint.comp (total N)

theorem domainGram_of_mem_H {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) : domainGram N h = gram N t h :=
  total_adjoint_total_of_mem_H hh

theorem domainGram_mem_H {N t : ℕ} {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) : domainGram N h ∈ H N t := by
  rw [domainGram_of_mem_H hh]
  exact HarmonicGram.gram_mem_H t hh

theorem domainGram_isSymmetric (N : ℕ) : (domainGram N).IsSymmetric := by
  intro h k
  change ⟪(total N).adjoint (total N h), k⟫_ℂ =
    ⟪h, (total N).adjoint (total N k)⟫_ℂ
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

@[simp] theorem adjoint_domainGram (N : ℕ) : (domainGram N).adjoint = domainGram N :=
  (domainGram_isSymmetric N).adjoint_eq

theorem domainGram_projection (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    domainGram N ((H N t).starProjection h) = (H N t).starProjection (domainGram N h) := by
  symm
  apply (H N t).eq_starProjection_of_mem_of_inner_eq_zero
  · exact domainGram_mem_H ((H N t).starProjection_apply_mem h)
  · intro k hk
    rw [← map_sub, domainGram_isSymmetric N]
    exact (H N t).starProjection_inner_eq_zero h _ (domainGram_mem_H hk)

/-- The actual domain Gram commutes with every exact harmonic degree projection. -/
theorem domainGram_commutes_projection (N t : ℕ) :
    (domainGram N).comp (H N t).starProjection.toLinearMap =
      (H N t).starProjection.toLinearMap.comp (domainGram N) := by
  apply LinearMap.ext
  intro h
  exact domainGram_projection N t h

end QuantumOracle.RawDegree
