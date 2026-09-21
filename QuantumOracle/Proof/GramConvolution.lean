import QuantumOracle.Proof.GramFiltration
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The actual extension Gram operator as central group-algebra convolution

The coefficient equivalence sends the actual permutation ket to the matching
group-algebra basis element. With this orientation the Gram operator is right
multiplication by its identity column. Actual two-sided relabeling equivariance
makes this element central, so left multiplication gives the same operator.
No representation decomposition or scalar eigenvalue is assumed.
-/

noncomputable section

namespace QuantumOracle.GramConvolution

open PermutationExtensions GramFiltration KernelEquivariance
open scoped BigOperators

abbrev GroupAlgebra (N : ℕ) := MonoidAlgebra ℂ (Perm N)

/-- Preserve the actual permutation coefficients when passing to the group algebra. -/
def equiv (N : ℕ) : EuclideanSpace ℂ (Perm N) ≃ₗ[ℂ] GroupAlgebra N :=
  (WithLp.linearEquiv 2 ℂ (Perm N → ℂ)).trans
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Perm N)).symm.trans
      (MonoidAlgebra.coeffLinearEquiv ℂ).symm)

@[simp] theorem equiv_coeff (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) (π : Perm N) :
    (equiv N h).coeff π = h π := rfl

@[simp] theorem equiv_single (N : ℕ) (π : Perm N) (a : ℂ) :
    equiv N (EuclideanSpace.single π a) = MonoidAlgebra.single π a := by
  classical
  ext σ
  simp [equiv_coeff, PiLp.single_apply, Finsupp.single_apply, eq_comm]

/-- Relabeling the output is actual left multiplication by a permutation. -/
theorem equiv_relabel_left (N : ℕ) (π : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    equiv N (relabelOperator (Equiv.refl _) π h) =
      MonoidAlgebra.of ℂ (Perm N) π * equiv N h := by
  ext σ
  rw [equiv_coeff, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
    equiv_coeff, one_mul]
  change h (((Equiv.refl _).trans σ).trans π.symm) = h (π⁻¹ * σ)
  rfl

/-- Relabeling the input in this direction is actual right multiplication. -/
theorem equiv_relabel_right (N : ℕ) (π : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    equiv N (relabelOperator π.symm (Equiv.refl _) h) =
      equiv N h * MonoidAlgebra.of ℂ (Perm N) π := by
  ext σ
  rw [equiv_coeff, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply,
    equiv_coeff, mul_one]
  change h ((π.symm.trans σ).trans (Equiv.refl _).symm) = h (σ * π⁻¹)
  rfl

/-- The convolution element is the actual Gram operator's identity column. -/
def kernel (N t : ℕ) : GroupAlgebra N :=
  equiv N (gram N t (EuclideanSpace.single (Equiv.refl _) 1))

theorem kernel_coeff (N t : ℕ) (π : Perm N) :
    (kernel N t).coeff π =
      ((Nat.choose (Fintype.card {x : Fin N // π.symm x = x}) t : ℕ) : ℂ) /
        ((N - t).factorial : ℂ) := by
  rw [kernel, equiv_coeff]
  simpa only [gram, Equiv.refl_trans] using
    ExtensionOperator.T_adjoint_basis_entry t π (Equiv.refl _)

private theorem sum_single (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    ∑ π : Perm N, h π • EuclideanSpace.single π 1 = h := by
  classical
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Perm N) ℂ).sum_repr h

theorem sum_coeff_basis (N : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    ∑ π : Perm N, h π • MonoidAlgebra.of ℂ (Perm N) π = equiv N h := by
  have he := congrArg (equiv N) (sum_single N h)
  simpa only [map_sum, map_smul, equiv_single, MonoidAlgebra.of_apply] using he

/-- The actual Gram map is right convolution with its actual identity column. -/
theorem equiv_gram (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    equiv N (gram N t h) = equiv N h * kernel N t := by
  calc
    equiv N (gram N t h) =
        ∑ π : Perm N, h π • (MonoidAlgebra.of ℂ (Perm N) π * kernel N t) := by
      conv_lhs => rw [← sum_single N h]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro π _
      rw [gram_single_from_identity, equiv_relabel_left]
      rfl
    _ = (∑ π : Perm N, h π • MonoidAlgebra.of ℂ (Perm N) π) * kernel N t := by
      rw [Finset.sum_mul]
      simp only [smul_mul_assoc]
    _ = equiv N h * kernel N t := by rw [sum_coeff_basis]

/-- Two-sided actual relabeling equivariance forces the convolution element to
commute with every actual permutation basis element. -/
theorem kernel_commutes_basis (N t : ℕ) (π : Perm N) :
    kernel N t * MonoidAlgebra.of ℂ (Perm N) π =
      MonoidAlgebra.of ℂ (Perm N) π * kernel N t := by
  have hc := LinearMap.congr_fun (T_adjoint_commutes t π.symm (Equiv.refl _))
    (EuclideanSpace.single (Equiv.refl _) 1)
  change gram N t (relabelOperator π.symm (Equiv.refl _)
      (EuclideanSpace.single (Equiv.refl _) 1)) =
    relabelOperator π.symm (Equiv.refl _)
      (gram N t (EuclideanSpace.single (Equiv.refl _) 1)) at hc
  simp only [relabelOperator_single, Equiv.symm_symm, Equiv.trans_refl] at hc
  have he := congrArg (equiv N) hc
  rw [equiv_gram, equiv_single, equiv_relabel_right] at he
  exact he.symm

theorem kernel_commutes (N t : ℕ) (a : GroupAlgebra N) :
    kernel N t * a = a * kernel N t := by
  induction a using MonoidAlgebra.induction_on with
  | hM π => exact kernel_commutes_basis N t π
  | hadd a b ha hb => rw [mul_add, add_mul, ha, hb]
  | hsmul c a ha => rw [mul_smul_comm, smul_mul_assoc, ha]

theorem kernel_mem_center (N t : ℕ) :
    kernel N t ∈ Subalgebra.center ℂ (GroupAlgebra N) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  exact (kernel_commutes N t a).symm

/-- Centrality also identifies Gram with left multiplication on the actual algebra. -/
theorem equiv_gram_left (N t : ℕ) (h : EuclideanSpace ℂ (Perm N)) :
    equiv N (gram N t h) = kernel N t * equiv N h := by
  rw [equiv_gram, kernel_commutes]

/-- Any actual left ideal, including a constructed Specht ideal, is preserved
after transport back to the permutation register. -/
theorem gram_mem_leftIdeal (N t : ℕ)
    (V : Submodule (GroupAlgebra N) (GroupAlgebra N))
    {h : EuclideanSpace ℂ (Perm N)} (hh : equiv N h ∈ V) :
    equiv N (gram N t h) ∈ V := by
  rw [equiv_gram_left]
  exact V.smul_mem (kernel N t) hh

end QuantumOracle.GramConvolution
