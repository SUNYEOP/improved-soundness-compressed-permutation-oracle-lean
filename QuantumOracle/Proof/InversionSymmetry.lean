import QuantumOracle.Model.RawEmbedding
import QuantumOracle.Model.Query

/-!
# Actual inversion symmetry of the knowledge layers and raw embedding

Permutation inversion and database graph inversion are concrete basis
permutations. Their intertwining properties are proved for the actual
consistent-state spans, orthogonal degree projections, and raw assembly.
-/

noncomputable section

namespace QuantumOracle.InversionSymmetry

open PermutationExtensions
open scoped BigOperators InnerProductSpace

variable {N t : ℕ}

def permutationInverse (N : ℕ) : Equiv.Perm (Perm N) where
  toFun := Equiv.symm
  invFun := Equiv.symm
  left_inv := Equiv.symm_symm
  right_inv := Equiv.symm_symm

def databaseInverse (N : ℕ) : Equiv.Perm (Database N) where
  toFun := Database.inverse
  invFun := Database.inverse
  left_inv := Database.inverse_inverse
  right_inv := Database.inverse_inverse

/-- Actual inversion of the exact permutation register. -/
def oracle (N : ℕ) : EuclideanSpace ℂ (Perm N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Perm N) :=
  Query.linearLift (permutationInverse N)

/-- Actual inversion of the partial-injection database register. -/
def database (N : ℕ) : Compression.State N ≃ₗᵢ[ℂ] Compression.State N :=
  Query.linearLift (databaseInverse N)

@[simp] theorem oracle_apply (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) (π : Perm N) :
    oracle N h π = h π.symm := rfl

@[simp] theorem database_apply (N : ℕ) (ψ : Compression.State N) (I : Database N) :
    database N ψ I = ψ I.inverse := rfl

@[simp] theorem oracle_involutive (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    oracle N (oracle N h) = h := by ext π; simp

@[simp] theorem database_involutive (N : ℕ) (ψ : Compression.State N) :
    database N (database N ψ) = ψ := by
  ext I
  change ψ I.inverse.inverse = ψ I
  exact congrArg (fun J => ψ J) (Database.inverse_inverse I)

theorem oracle_inner_right (N : ℕ) (h k : EuclideanSpace ℂ (Perm N)) :
    ⟪h, oracle N k⟫_ℂ = ⟪oracle N h, k⟫_ℂ := by
  simpa only [oracle_involutive] using (oracle N).inner_map_map (oracle N h) k

/-- Inversion sends each actual consistent state to the inverted database state. -/
@[simp] theorem oracle_vector (I : Database N) :
    oracle N (ConsistentState.vector I) = ConsistentState.vector I.inverse := by
  ext π
  simpa only [oracle_apply, Equiv.symm_symm] using
    (ConsistentState.vector_inverse_apply I π.symm).symm

theorem oracle_mem_K (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ KnowledgeSpace.K N t) : oracle N h ∈ KnowledgeSpace.K N t := by
  apply Submodule.span_induction (p := fun h _ => oracle N h ∈ KnowledgeSpace.K N t)
    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨I, rfl⟩
    rw [oracle_vector]
    exact KnowledgeSpace.vector_mem I.val.inverse (I.val.inverse_size.trans I.property)
  · simp
  · intro h k _ _ hh hk
    simpa using (KnowledgeSpace.K N t).add_mem hh hk
  · intro c h _ hh
    simpa using (KnowledgeSpace.K N t).smul_mem c hh

@[simp] theorem oracle_mem_K_iff (h : EuclideanSpace ℂ (Perm N)) :
    oracle N h ∈ KnowledgeSpace.K N t ↔ h ∈ KnowledgeSpace.K N t := by
  constructor
  · intro hh
    simpa only [oracle_involutive] using oracle_mem_K (oracle N h) hh
  · exact oracle_mem_K h

/-- An invariant subspace has an invariant orthogonal complement under inversion. -/
theorem oracle_mem_orthogonal (S : Submodule ℂ (EuclideanSpace ℂ (Perm N)))
    (hS : ∀ h, h ∈ S → oracle N h ∈ S) (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ Sᗮ) : oracle N h ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [oracle_inner_right]
  exact Submodule.inner_right_of_mem_orthogonal (hS k hk) hh

theorem oracle_mem_H (h : EuclideanSpace ℂ (Perm N))
    (hh : h ∈ HarmonicLayers.H N t) : oracle N h ∈ HarmonicLayers.H N t := by
  cases t with
  | zero => exact oracle_mem_K h hh
  | succ t =>
    exact ⟨oracle_mem_K h hh.1,
      oracle_mem_orthogonal _ (fun k hk => oracle_mem_K k hk) h hh.2⟩

@[simp] theorem oracle_mem_H_iff (h : EuclideanSpace ℂ (Perm N)) :
    oracle N h ∈ HarmonicLayers.H N t ↔ h ∈ HarmonicLayers.H N t := by
  constructor
  · intro hh
    simpa only [oracle_involutive] using oracle_mem_H (oracle N h) hh
  · exact oracle_mem_H h

theorem map_H (N t : ℕ) :
    (HarmonicLayers.H N t).map (oracle N).toLinearEquiv.toLinearMap = HarmonicLayers.H N t := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact oracle_mem_H h hh
  · intro h hh
    exact ⟨oracle N h, oracle_mem_H h hh, oracle_involutive N h⟩

/-- Inversion commutes with every actual harmonic-layer projection. -/
theorem oracle_projection (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    oracle N ((HarmonicLayers.H N t).starProjection h) =
      (HarmonicLayers.H N t).starProjection (oracle N h) := by
  have hp := (oracle N).toLinearIsometry.map_starProjection (HarmonicLayers.H N t) h
  change oracle N ((HarmonicLayers.H N t).starProjection h) =
    ((HarmonicLayers.H N t).map (oracle N).toLinearEquiv.toLinearMap).starProjection
      (oracle N h) at hp
  simpa only [map_H] using hp

/-- Each actual level adjoint intertwines permutation and database inversion. -/
theorem raw_intertwines (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    RawHarmonic.raw N t (oracle N h) = database N (RawHarmonic.raw N t h) := by
  ext I
  rw [database_apply]
  by_cases hI : I.size = t
  · rw [RawHarmonic.raw_apply_of_size N t _ I hI,
      RawHarmonic.raw_apply_of_size N t _ I.inverse (I.inverse_size.trans hI),
      oracle_inner_right, oracle_vector]
  · rw [RawHarmonic.raw_apply_of_ne N t _ I hI,
      RawHarmonic.raw_apply_of_ne N t _ I.inverse (by simpa using hI)]

/-- The full actual raw assembly has the same inversion intertwiner. -/
theorem total_intertwines (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    RawEmbedding.total N (oracle N h) = database N (RawEmbedding.total N h) := by
  rw [RawEmbedding.total_apply, RawEmbedding.total_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← oracle_projection, raw_intertwines]

end QuantumOracle.InversionSymmetry
