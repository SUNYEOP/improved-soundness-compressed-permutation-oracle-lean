import QuantumOracle.Proof.Conditioning
import QuantumOracle.Model.CompressionAction

/-!
# Exact uniform initialization of actual conditioning

The concrete residual conditioning map sends the uniform permutation state to
the actual compressed empty-database state. This is an exact degree-zero fact;
it supplies no positive-degree comparison bound.
-/

noncomputable section

namespace QuantumOracle.ConditioningInitialization

open PermutationExtensions
open scoped BigOperators

variable {N : ℕ}

private theorem sum_apply {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (a : α) : (∑ i, v i) a = ∑ i, v i a :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : α => ℂ) a) v Finset.univ

theorem uniform_amplitude_split (x : Fin (N + 1)) :
    UniformState.amplitude (Perm (N + 1)) =
      UniformState.amplitude (Fin (N + 1)) * UniformState.amplitude (Perm N) := by
  unfold UniformState.amplitude
  rw [Fintype.card_congr (ResidualPermutation.answerProductEquiv x),
    Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]

/-- Each actual answer sector of the full uniform state is the correctly scaled
uniform state on residual permutations. -/
theorem uniform_slice (x y : Fin (N + 1)) :
    WorkspaceKnowledge.slice
      (ResidualPermutation.reindex x (ConsistentState.vector Database.empty)) y =
      (UniformState.amplitude (Fin (N + 1)) : ℂ) •
        ConsistentState.vector (Database.empty : Database N) := by
  ext σ
  change ConsistentState.vector Database.empty (ResidualPermutation.insert x y σ) = _
  simp only [ConsistentState.vector_empty_eq_uniform, UniformState.uniform_apply,
    PiLp.smul_apply, smul_eq_mul]
  exact_mod_cast uniform_amplitude_split x

theorem jointIota_single (x y : Fin (N + 1)) (I : Database N) (c : ℂ) :
    ResidualDatabase.jointIota x (EuclideanSpace.single (y, I) c) =
      EuclideanSpace.single (ResidualDatabase.insert x y I) c := by
  classical
  ext K
  by_cases hK : K ∈ Set.range (ResidualDatabase.jointInsert x)
  · obtain ⟨⟨z, J⟩, rfl⟩ := hK
    rw [ResidualDatabase.jointInsert, ResidualDatabase.jointIota_apply_insert]
    simp only [EuclideanSpace.single_apply]
    change (if (z, J) = (y, I) then c else 0) =
      (if ResidualDatabase.jointInsert x (z, J) = ResidualDatabase.jointInsert x (y, I)
        then c else 0)
    simp only [(ResidualDatabase.jointInsert_injective x).eq_iff]
  · rw [ResidualDatabase.jointIota_apply_of_notMem x _ K hK]
    have hne : K ≠ ResidualDatabase.insert x y I := by
      rintro rfl
      exact hK ⟨(y, I), rfl⟩
    simp [EuclideanSpace.single_apply, hne]

theorem insert_empty (x y : Fin (N + 1)) :
    ResidualDatabase.insert x y Database.empty =
      (Database.empty : Database (N + 1)).set x y := by
  have h : ResidualDatabase.lift x y Database.empty = Database.empty := by
    apply Database.ext
    simp [ResidualDatabase.lift]
  rw [ResidualDatabase.insert, h]

/-- Actual conditioning of the uniform state is the normalized one-edge sum. -/
theorem J_uniform_eq_sum (x : Fin (N + 1)) :
    Conditioning.J x (ConsistentState.vector Database.empty) =
      ∑ y : Fin (N + 1), EuclideanSpace.single
        ((Database.empty : Database (N + 1)).set x y)
        (UniformState.amplitude (Fin (N + 1)) : ℂ) := by
  classical
  have hvec : HiddenIsometry.onOracle (Fin (N + 1)) (PolarEmbedding.candidate N)
      (ResidualPermutation.reindex x (ConsistentState.vector Database.empty)) =
      ∑ y : Fin (N + 1), EuclideanSpace.single (y, (Database.empty : Database N))
        (UniformState.amplitude (Fin (N + 1)) : ℂ) := by
    ext ⟨y, I⟩
    rw [HiddenIsometry.onOracle_apply, uniform_slice, map_smul,
      PolarEmbedding.candidate_uniform, sum_apply]
    by_cases hI : I = Database.empty
    · subst I
      simp [EuclideanSpace.single_apply, Prod.mk.injEq]
    · simp [EuclideanSpace.single_apply, Prod.mk.injEq, hI]
  rw [Conditioning.J_apply, hvec, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [jointIota_single, insert_empty]

def emptyBase (x : Fin (N + 1)) : CompressionIndex.Base x :=
  ⟨Database.empty, by simp⟩

theorem J_uniform_eq_plusState (x : Fin (N + 1)) :
    Conditioning.J x (ConsistentState.vector Database.empty) =
      Compression.plusState x (emptyBase x) := by
  classical
  let e : CompressionIndex.Fresh (Database.empty : Database (N + 1)) ≃ Fin (N + 1) :=
    { toFun := Subtype.val
      invFun := fun y => ⟨y, by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hamp : UniformState.amplitude (CompressionIndex.Fresh (Database.empty : Database (N + 1))) =
      UniformState.amplitude (Fin (N + 1)) := by
    unfold UniformState.amplitude
    rw [CompressionIndex.card_fresh, Database.empty_size, Nat.sub_zero, Fintype.card_fin]
  rw [J_uniform_eq_sum, Compression.plusState_eq_sum]
  change (∑ y : Fin (N + 1), EuclideanSpace.single (Database.empty.set x y)
      (UniformState.amplitude (Fin (N + 1)) : ℂ)) =
    ∑ y : CompressionIndex.Fresh (Database.empty : Database (N + 1)),
      EuclideanSpace.single (Database.empty.set x y.val)
        (UniformState.amplitude (CompressionIndex.Fresh (Database.empty : Database (N + 1))) : ℂ)
  rw [hamp]
  exact (e.sum_comp (fun y => EuclideanSpace.single (Database.empty.set x y)
    (UniformState.amplitude (Fin (N + 1)) : ℂ))).symm

/-- At degree zero the actual conditioning comparison is exact. -/
theorem J_uniform_eq_pC_empty (x : Fin (N + 1)) :
    Conditioning.J x (ConsistentState.vector Database.empty) =
      Compression.pC x (Compression.ket Database.empty) := by
  rw [J_uniform_eq_plusState]
  exact (Compression.pC_ket_base x (emptyBase x)).symm

end QuantumOracle.ConditioningInitialization
