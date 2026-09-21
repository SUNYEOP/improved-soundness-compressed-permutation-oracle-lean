import QuantumOracle.Proof.ConditioningError
import QuantumOracle.Proof.ConditioningInverseComparison
import QuantumOracle.Model.AnswerSelection

/-!
# Conditional local error bounds for the actual query operators

`Bound` is an explicit numerical premise about the constructed conditioning
and compression maps on the actual knowledge space. One query increases that
space by at most one level. The proved two-error reductions therefore turn a
bound on level `t + 1` into an actual ordinary or marked query error of at most
`2 * ε`, including inverse queries and arbitrary entangled answer registers.
The numerical premise is not established by this module.
-/

noncomputable section

namespace QuantumOracle.ConditioningLocalBound

open BasisLookup PermutationExtensions WorkspaceKnowledge HiddenIsometry KnowledgeSpace

attribute [local irreducible] PolarEmbedding.candidate

variable {N t w : ℕ}

/-- A uniform numerical bound for the actual single-register conditioning discrepancy. -/
def Bound (N s : ℕ) (ε : ℝ) : Prop :=
  ∀ x : Fin (N + 1), ∀ h ∈ K (N + 1) s,
    ‖Conditioning.J x h - Compression.pC x (PolarEmbedding.candidate (N + 1) h)‖ ≤
      ε * ‖h‖

/-- Actual ordinary queries select answer-dependent oracle slices. -/
theorem ordinary_supported_succ (encode : Encoding N w) (inverse : Bool) (x : Fin N)
    (ht : t < N) {ψ : EuclideanSpace ℂ (Bits w × Perm N)}
    (hψ : Supported (K N t) ψ) :
    Supported (K N (t + 1)) (Query.exactOrdinary encode inverse x ψ) := by
  intro z
  have hs : slice (Query.exactOrdinary encode inverse x ψ) z =
      AnswerSelection.select inverse x (fun y => slice ψ (xor z (encode y))) := by
    ext π
    rfl
  rw [hs]
  exact AnswerSelection.select_mem_succ ht inverse x _ (fun y => hψ (xor z (encode y)))

/-- Marked queries have the same actual one-step degree growth for either direction. -/
theorem marked_supported_succ (encode : Encoding N w) (inverse : Bool) (x : Fin N)
    (ht : t < N) {ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm N)}
    (hψ : Supported (K N t) ψ) :
    Supported (K N (t + 1)) (Query.exactMarked encode inverse x ψ) := by
  intro z
  have hs : slice (Query.exactMarked encode inverse x ψ) z =
      AnswerSelection.select inverse x
        (fun y => slice ψ (Bool.xor z.1 true, xor z.2 (encode y))) := by
    ext π
    rfl
  rw [hs]
  exact AnswerSelection.select_mem_succ ht inverse x _
    (fun y => hψ (Bool.xor z.1 true, xor z.2 (encode y)))

/-- Inversion preserves actual knowledge support, including all workspace entanglement. -/
theorem inversion_supported {A : Type*} [Fintype A]
    {ψ : EuclideanSpace ℂ (A × Perm N)} (hψ : Supported (K N t) ψ) :
    Supported (K N t) (onOracle A (InversionSymmetry.oracle N).toLinearIsometry ψ) := by
  intro a
  rw [slice_onOracle]
  exact InversionSymmetry.oracle_mem_K _ (hψ a)

theorem ordinary_forward_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε) (ht : t < N + 1)
    {ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖CompressedQuery.ordinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactOrdinary encode false x ψ)‖ ≤ (2 * ε) * ‖ψ‖ := by
  have hb := ConditioningError.error_le_of_supported_K x ε hε (hbound x)
    (supported_mono (KnowledgeSpace.le_succ ht) hψ)
  have ha := ConditioningError.error_le_of_supported_K x ε hε (hbound x)
    (ordinary_supported_succ encode false x ht hψ)
  have he := (ConditioningComparison.ordinary_error_le encode x ψ).trans (add_le_add hb ha)
  rw [(Query.exactOrdinary encode false x).norm_map] at he
  nlinarith

theorem marked_forward_error_le (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε) (ht : t < N + 1)
    {ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖CompressedQuery.marked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactMarked encode false x ψ)‖ ≤ (2 * ε) * ‖ψ‖ := by
  have hb := ConditioningError.error_le_of_supported_K x ε hε (hbound x)
    (supported_mono (KnowledgeSpace.le_succ ht) hψ)
  have ha := ConditioningError.error_le_of_supported_K x ε hε (hbound x)
    (marked_supported_succ encode false x ht hψ)
  have he := (ConditioningComparison.marked_error_le encode x ψ).trans (add_le_add hb ha)
  rw [(Query.exactMarked encode false x).norm_map] at he
  nlinarith

/-- The actual ordinary query error is bounded uniformly in the query direction. -/
theorem ordinary_error_le (encode : Encoding (N + 1) w) (inverse : Bool)
    (x : Fin (N + 1)) (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε)
    (ht : t < N + 1) {ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖(if inverse then CompressedQuery.inverseOrdinary encode x
        else CompressedQuery.ordinary encode x)
        (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactOrdinary encode inverse x ψ)‖ ≤ (2 * ε) * ‖ψ‖ := by
  cases inverse
  · exact ordinary_forward_error_le encode x ε hε hbound ht hψ
  · change ‖CompressedQuery.inverseOrdinary encode x
        (onOracle (Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactOrdinary encode true x ψ)‖ ≤ _
    rw [ConditioningInverseComparison.inverse_ordinary_error_eq]
    have he := ordinary_forward_error_le encode x ε hε hbound ht (inversion_supported hψ)
    simpa only [LinearIsometry.norm_map] using he

/-- The actual marked query has the same bound, with arbitrary initial marker and answer. -/
theorem marked_error_le (encode : Encoding (N + 1) w) (inverse : Bool)
    (x : Fin (N + 1)) (ε : ℝ) (hε : 0 ≤ ε) (hbound : Bound N (t + 1) ε)
    (ht : t < N + 1) {ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))}
    (hψ : Supported (K (N + 1) t) ψ) :
    ‖(if inverse then CompressedQuery.inverseMarked encode x
        else CompressedQuery.marked encode x)
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactMarked encode inverse x ψ)‖ ≤ (2 * ε) * ‖ψ‖ := by
  cases inverse
  · exact marked_forward_error_le encode x ε hε hbound ht hψ
  · change ‖CompressedQuery.inverseMarked encode x
        (onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1)) ψ) -
      onOracle (Bool × Bits w) (PolarEmbedding.candidate (N + 1))
        (Query.exactMarked encode true x ψ)‖ ≤ _
    rw [ConditioningInverseComparison.inverse_marked_error_eq]
    have he := marked_forward_error_le encode x ε hε hbound ht (inversion_supported hψ)
    simpa only [LinearIsometry.norm_map] using he

end QuantumOracle.ConditioningLocalBound
