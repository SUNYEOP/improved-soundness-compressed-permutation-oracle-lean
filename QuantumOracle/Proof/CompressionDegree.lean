import QuantumOracle.Proof.PolarDegree

/-!
# Exact degree components of actual compression

For a cancelling state at physical database degree `t`, the degree-`t` output
of compression is its already-defined part. Its other component is the actual
compression of the undefined part, at degree `t + 1`. In particular these
identities apply to the constructed positive polar map on `H N t`; they need
no spectral scalar or overlap assumption.
-/

noncomputable section

namespace QuantumOracle.CompressionDegree

open Compression CompressionIndex CompressionCancellation DatabaseDegree
open PermutationExtensions HarmonicLayers
open scoped BigOperators InnerProductSpace

variable {N s t : ℕ}

theorem definedPart_mem_exactLevel (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) : definedPart x ψ ∈ exactLevel N t := by
  intro I hI
  simp [definedPart_apply, hψ I hI]

theorem undefinedPart_mem_exactLevel (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) : undefinedPart x ψ ∈ exactLevel N t := by
  intro I hI
  simp [undefinedPart_apply, hψ I hI]

/-- An undefined pure-size state is extended by exactly one actual database edge. -/
theorem pC_undefinedPart_mem_succ (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) :
    pC x (undefinedPart x ψ) ∈ exactLevel N (t + 1) := by
  intro I hI
  obtain ⟨⟨J, o⟩, rfl⟩ := decode_surjective x I
  cases o with
  | none =>
    change coordinates x (pC x (undefinedPart x ψ)) J none = 0
    rw [coordinates_pC_undefinedPart]
    simp
  | some y =>
    have hbase : J.val.size ≠ t := by
      intro heq
      apply hI
      rw [decode_some_size, heq]
    change coordinates x (pC x (undefinedPart x ψ)) J (some y) = 0
    rw [coordinates_pC_undefinedPart, hψ J.val hbase, zero_smul]
    rfl

theorem project_eq_zero_of_mem_exactLevel (hst : s ≠ t) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) : project N s ψ = 0 := by
  ext I
  by_cases hI : I.size = s
  · rw [project_apply, if_pos hI, hψ I (fun ht => hst (hI.symm.trans ht))]
    rfl
  · simp [hI]

theorem inner_eq_zero_of_mem_exactLevel (hst : s ≠ t) {ψ φ : State N}
    (hψ : ψ ∈ exactLevel N s) (hφ : φ ∈ exactLevel N t) :
    ⟪ψ, φ⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro I _
  by_cases hI : I.size = s
  · rw [hφ I (fun ht => hst (hI.symm.trans ht)), inner_zero_right]
  · rw [hψ I hI, inner_zero_left]

/-- The original-degree component is precisely the already-defined part. -/
theorem project_pC_of_cancels (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) (hc : Cancels x ψ) :
    project N t (pC x ψ) = definedPart x ψ := by
  rw [pC_eq_defined_add x ψ hc, map_add,
    (project_eq_self_iff N t _).mpr (definedPart_mem_exactLevel x hψ),
    project_eq_zero_of_mem_exactLevel (Nat.ne_of_lt (Nat.lt_succ_self t))
      (pC_undefinedPart_mem_succ x hψ), add_zero]

/-- The next-degree component is precisely compression of the undefined part. -/
theorem project_succ_pC_of_cancels (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) (hc : Cancels x ψ) :
    project N (t + 1) (pC x ψ) = pC x (undefinedPart x ψ) := by
  rw [pC_eq_defined_add x ψ hc, map_add,
    project_eq_zero_of_mem_exactLevel (Nat.ne_of_gt (Nat.lt_succ_self t))
      (definedPart_mem_exactLevel x hψ),
    (project_eq_self_iff N (t + 1) _).mpr (pC_undefinedPart_mem_succ x hψ), zero_add]

theorem definedPart_inner_pC_undefinedPart (x : Fin N) {ψ : State N}
    (hψ : ψ ∈ exactLevel N t) :
    ⟪definedPart x ψ, pC x (undefinedPart x ψ)⟫_ℂ = 0 :=
  inner_eq_zero_of_mem_exactLevel (Nat.ne_of_lt (Nat.lt_succ_self t))
    (definedPart_mem_exactLevel x hψ) (pC_undefinedPart_mem_succ x hψ)

theorem definedPart_candidate_mem (x : Fin N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) :
    definedPart x (PolarEmbedding.candidate N h) ∈ exactLevel N t :=
  definedPart_mem_exactLevel x (PolarDegree.candidate_mem_exactLevel hh)

theorem pC_undefinedPart_candidate_mem (x : Fin N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) :
    pC x (undefinedPart x (PolarEmbedding.candidate N h)) ∈ exactLevel N (t + 1) :=
  pC_undefinedPart_mem_succ x (PolarDegree.candidate_mem_exactLevel hh)

theorem project_pC_candidate (x : Fin N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) :
    project N t (pC x (PolarEmbedding.candidate N h)) =
      definedPart x (PolarEmbedding.candidate N h) :=
  project_pC_of_cancels x (PolarDegree.candidate_mem_exactLevel hh)
    (PolarEmbedding.candidate_cancels x h)

theorem project_succ_pC_candidate (x : Fin N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) :
    project N (t + 1) (pC x (PolarEmbedding.candidate N h)) =
      pC x (undefinedPart x (PolarEmbedding.candidate N h)) :=
  project_succ_pC_of_cancels x (PolarDegree.candidate_mem_exactLevel hh)
    (PolarEmbedding.candidate_cancels x h)

/-- Orthogonality of the two explicit physical output components. -/
theorem candidate_components_inner_eq_zero (x : Fin N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    ⟪definedPart x (PolarEmbedding.candidate N h),
      pC x (undefinedPart x (PolarEmbedding.candidate N h))⟫_ℂ = 0 :=
  definedPart_inner_pC_undefinedPart x (PolarDegree.candidate_mem_exactLevel hh)

/-- Actual compression equals the sum of its two physical degree projections. -/
theorem pC_candidate_decomposition (x : Fin N) {h : EuclideanSpace ℂ (Perm N)}
    (hh : h ∈ H N t) :
    pC x (PolarEmbedding.candidate N h) =
      project N t (pC x (PolarEmbedding.candidate N h)) +
        project N (t + 1) (pC x (PolarEmbedding.candidate N h)) := by
  rw [project_pC_candidate x hh, project_succ_pC_candidate x hh]
  exact pC_eq_defined_add x _ (PolarEmbedding.candidate_cancels x h)

theorem candidate_components_norm_sq (x : Fin N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ H N t) :
    ‖definedPart x (PolarEmbedding.candidate N h)‖ ^ 2 +
      ‖pC x (undefinedPart x (PolarEmbedding.candidate N h))‖ ^ 2 = ‖h‖ ^ 2 := by
  simp only [pow_two]
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (candidate_components_inner_eq_zero x hh),
    ← pC_eq_defined_add x _ (PolarEmbedding.candidate_cancels x h),
    (pC x).norm_map, (PolarEmbedding.candidate N).norm_map]

end QuantumOracle.CompressionDegree
