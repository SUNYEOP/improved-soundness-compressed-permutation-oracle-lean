import QuantumOracle.Proof.ResidualPermutation
import QuantumOracle.Proof.ResidualDatabase
import QuantumOracle.Model.PolarEmbedding
import QuantumOracle.Model.HiddenIsometry

/-!
# Actual conditioning maps from residual permutation registers

The exact permutation is first split into its answer at x and its residual
permutation. The actual polar isometry embeds the residual register, and the
actual residual-database insertion adjoins the recorded answer edge. The result
is a genuine isometry J, with a corresponding isometry D on the actual global
polar image. No query-comparison estimate is assumed here.
-/

noncomputable section

namespace QuantumOracle.Conditioning

open PermutationExtensions
open scoped InnerProductSpace

variable {N : ℕ}

attribute [local irreducible] PolarEmbedding.candidate

/-- Actual conditioning: answer decomposition, residual polar map, and edge insertion. -/
def J (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Perm (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database (N + 1)) :=
  (ResidualDatabase.jointIota x).comp
    ((HiddenIsometry.onOracle (Fin (N + 1)) (PolarEmbedding.candidate N)).comp
      (ResidualPermutation.reindex x).toLinearIsometry)

theorem J_apply (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    J x h = ResidualDatabase.jointIota x
      (HiddenIsometry.onOracle (Fin (N + 1)) (PolarEmbedding.candidate N)
        (ResidualPermutation.reindex x h)) := rfl

/-- The coefficient on an actual inserted edge graph is the residual polar coefficient. -/
@[simp] theorem J_apply_insert (x y : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (I : Database N) :
    J x h (ResidualDatabase.insert x y I) =
      PolarEmbedding.candidate N (WorkspaceKnowledge.slice (ResidualPermutation.reindex x h) y) I := by
  rw [J_apply, ResidualDatabase.jointIota_apply_insert, HiddenIsometry.onOracle_apply]

theorem J_apply_of_notMem (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (I : Database (N + 1))
    (hI : I ∉ Set.range (ResidualDatabase.jointInsert x)) : J x h I = 0 := by
  rw [J_apply, ResidualDatabase.jointIota_apply_of_notMem x _ I hI]

/-- Every database carrying a nonzero conditioning amplitude records the queried input. -/
theorem J_apply_of_undefined (x : Fin (N + 1))
    (h : EuclideanSpace ℂ (Perm (N + 1))) (I : Database (N + 1))
    (hx : x ∉ I.domain) : J x h I = 0 := by
  apply J_apply_of_notMem
  rintro ⟨⟨y, K⟩, rfl⟩
  exact hx ((Database.mem_domain _ _).mpr ⟨y, ResidualDatabase.insert_contains x y K⟩)

theorem J_defines (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1)))
    (I : Database (N + 1)) (hI : J x h I ≠ 0) : x ∈ I.domain := by
  by_contra hx
  exact hI (J_apply_of_undefined x h I hx)

@[simp] theorem J_norm (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ‖J x h‖ = ‖h‖ := (J x).norm_map h

theorem J_inner (x : Fin (N + 1)) (h k : EuclideanSpace ℂ (Perm (N + 1))) :
    ⟪J x h, J x k⟫_ℂ = ⟪h, k⟫_ℂ := (J x).inner_map_map h k

/-- The actual global polar image, rather than an independently chosen subspace. -/
abbrev Image (N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Database N)) :=
  LinearMap.range (PolarEmbedding.candidate N).toLinearMap

local instance imageInnerProductSpace (N : ℕ) : InnerProductSpace ℂ ↥(Image N) :=
  inferInstance

/-- Conditioning on the actual polar image via its genuine inverse isometry. -/
def D (x : Fin (N + 1)) : Image (N + 1) →ₗᵢ[ℂ] EuclideanSpace ℂ (Database (N + 1)) :=
  (J x).comp (PolarEmbedding.candidate (N + 1)).equivRange.symm.toLinearIsometry

/-- The constructed D and J obey their defining comparison identity on every exact state. -/
@[simp] theorem D_candidate (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    D x ((PolarEmbedding.candidate (N + 1)).equivRange h) = J x h := by
  change J x ((PolarEmbedding.candidate (N + 1)).equivRange.symm
    ((PolarEmbedding.candidate (N + 1)).equivRange h)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem D_apply_candidate (x : Fin (N + 1)) (h : EuclideanSpace ℂ (Perm (N + 1))) :
    D x ⟨PolarEmbedding.candidate (N + 1) h, ⟨h, rfl⟩⟩ = J x h :=
  D_candidate x h

@[simp] theorem D_norm (x : Fin (N + 1)) (ψ : Image (N + 1)) : ‖D x ψ‖ = ‖ψ‖ :=
  (D x).norm_map ψ

theorem D_inner (x : Fin (N + 1)) (ψ φ : Image (N + 1)) :
    ⟪D x ψ, D x φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := (D x).inner_map_map ψ φ

theorem D_apply_of_undefined (x : Fin (N + 1)) (ψ : Image (N + 1))
    (I : Database (N + 1)) (hx : x ∉ I.domain) : D x ψ I = 0 :=
  J_apply_of_undefined x ((PolarEmbedding.candidate (N + 1)).equivRange.symm ψ) I hx

/-- The actual adjoint is the inverse on the actual isometric image. -/
@[simp] theorem candidate_adjoint_candidate (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    (PolarEmbedding.candidate N).toLinearMap.adjoint (PolarEmbedding.candidate N h) = h := by
  apply ext_inner_right ℂ
  intro k
  rw [LinearMap.adjoint_inner_left]
  exact (PolarEmbedding.candidate N).inner_map_map h k

/-- On its declared domain, D is precisely J composed with the actual W adjoint. -/
theorem D_eq_J_adjoint (x : Fin (N + 1)) (ψ : Image (N + 1)) :
    D x ψ = J x ((PolarEmbedding.candidate (N + 1)).toLinearMap.adjoint ψ.val) := by
  rcases ψ with ⟨_, ⟨h, rfl⟩⟩
  change D x ((PolarEmbedding.candidate (N + 1)).equivRange h) =
    J x ((PolarEmbedding.candidate (N + 1)).toLinearMap.adjoint
      (PolarEmbedding.candidate (N + 1) h))
  rw [D_candidate, candidate_adjoint_candidate]

end QuantumOracle.Conditioning
