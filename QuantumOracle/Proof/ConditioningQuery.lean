import QuantumOracle.Proof.Conditioning
import QuantumOracle.Proof.LookupCoordinates

/-!
# Actual lookup intertwining for the constructed conditioning isometry

Fixing the answer separates the exact query into residual sectors. The concrete
J map inserts that same answer into every output database. Consequently actual
ordinary and marked lookups intertwine, for arbitrary answer-register values
and arbitrary entangled input vectors. No comparison estimate is assumed.
-/

noncomputable section

namespace QuantumOracle.ConditioningQuery

open BasisLookup PermutationExtensions WorkspaceKnowledge HiddenIsometry

variable {N w : ℕ}

theorem reindex_slice_exactOrdinary (encode : Encoding (N + 1) w)
    (x y : Fin (N + 1)) (ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))) (z : Bits w) :
    slice (ResidualPermutation.reindex x (slice (Query.exactOrdinary encode false x ψ) z)) y =
      slice (ResidualPermutation.reindex x (slice ψ (xor z (encode y)))) y := by
  ext σ
  change Query.exactOrdinary encode false x ψ (z, ResidualPermutation.insert x y σ) =
    ψ (xor z (encode y), ResidualPermutation.insert x y σ)
  rw [LookupCoordinates.exactOrdinary_apply]
  change ψ (xor z (encode (ResidualPermutation.insert x y σ x)),
    ResidualPermutation.insert x y σ) = _
  rw [ResidualPermutation.insert_at]

theorem reindex_slice_exactMarked (encode : Encoding (N + 1) w)
    (x y : Fin (N + 1)) (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1)))
    (z : Bool × Bits w) :
    slice (ResidualPermutation.reindex x (slice (Query.exactMarked encode false x ψ) z)) y =
      slice (ResidualPermutation.reindex x
        (slice ψ (Bool.xor z.1 true, xor z.2 (encode y)))) y := by
  ext σ
  change Query.exactMarked encode false x ψ (z, ResidualPermutation.insert x y σ) =
    ψ ((Bool.xor z.1 true, xor z.2 (encode y)), ResidualPermutation.insert x y σ)
  rw [LookupCoordinates.exactMarked_apply]
  change ψ ((Bool.xor z.1 true, xor z.2 (encode (ResidualPermutation.insert x y σ x))),
    ResidualPermutation.insert x y σ) = _
  rw [ResidualPermutation.insert_at]

/-- The actual ordinary permutation lookup becomes the actual database lookup
after the constructed conditioning isometry. -/
theorem ordinary_intertwines (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ (Bits w × Perm (N + 1))) :
    onOracle (Bits w) (Conditioning.J x) (Query.exactOrdinary encode false x ψ) =
      Query.ordinaryLookup encode x (onOracle (Bits w) (Conditioning.J x) ψ) := by
  classical
  ext ⟨z, K⟩
  rw [onOracle_apply, LookupCoordinates.ordinary_apply, onOracle_apply]
  by_cases hK : K ∈ Set.range (ResidualDatabase.jointInsert x)
  · obtain ⟨⟨y, I⟩, rfl⟩ := hK
    dsimp only [ResidualDatabase.jointInsert]
    change Conditioning.J x _ (ResidualDatabase.insert x y I) =
      Conditioning.J x _ (ResidualDatabase.insert x y I)
    have ha : ordinaryAnswer encode (ResidualDatabase.insert x y I) x = encode y := by
      simp only [ordinaryAnswer,
        (Database.lookup_eq_some _ x y).mpr (ResidualDatabase.insert_contains x y I)]
    rw [Conditioning.J_apply_insert, Conditioning.J_apply_insert, ha,
      reindex_slice_exactOrdinary]
  · rw [Conditioning.J_apply_of_notMem x _ K hK,
      Conditioning.J_apply_of_notMem x _ K hK]

/-- The marked version includes an arbitrary initial marker and answer value. -/
theorem marked_intertwines (encode : Encoding (N + 1) w) (x : Fin (N + 1))
    (ψ : EuclideanSpace ℂ ((Bool × Bits w) × Perm (N + 1))) :
    onOracle (Bool × Bits w) (Conditioning.J x) (Query.exactMarked encode false x ψ) =
      Query.markedLookup encode x (onOracle (Bool × Bits w) (Conditioning.J x) ψ) := by
  classical
  ext ⟨z, K⟩
  rw [onOracle_apply, LookupCoordinates.marked_apply, onOracle_apply]
  by_cases hK : K ∈ Set.range (ResidualDatabase.jointInsert x)
  · obtain ⟨⟨y, I⟩, rfl⟩ := hK
    dsimp only [ResidualDatabase.jointInsert]
    change Conditioning.J x _ (ResidualDatabase.insert x y I) =
      Conditioning.J x _ (ResidualDatabase.insert x y I)
    have ha : markedAnswer encode (ResidualDatabase.insert x y I) x = (true, encode y) := by
      simp only [markedAnswer,
        (Database.lookup_eq_some _ x y).mpr (ResidualDatabase.insert_contains x y I)]
    rw [Conditioning.J_apply_insert, Conditioning.J_apply_insert, ha]
    exact congrArg (fun v => PolarEmbedding.candidate N v I)
      (reindex_slice_exactMarked encode x y ψ z)
  · rw [Conditioning.J_apply_of_notMem x _ K hK,
      Conditioning.J_apply_of_notMem x _ K hK]

end QuantumOracle.ConditioningQuery
