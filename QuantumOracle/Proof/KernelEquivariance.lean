import QuantumOracle.Model.ExtensionOperator
import QuantumOracle.Model.Query

/-!
# Operator equivariance of the extension kernel

The actual permutation-register relabeling sends `|π⟩` to `|β ∘ π ∘ α⁻¹⟩`,
as in the manuscript. Appendix A's simultaneous entry invariance is promoted
to equality of linear-map compositions with `T T†`. No irreducible decomposition,
Schur lemma, eigenvalue formula, or normalization of `W` is assumed or proved.
-/

noncomputable section

namespace QuantumOracle.KernelEquivariance

open PermutationExtensions ExtensionOperator

/-- Entry invariance under a basis permutation implies commutation of the actual
Euclidean linear map with the corresponding complex linear isometry. -/
theorem matrix_commutes_of_relabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (e : Equiv.Perm ι)
    (h : ∀ i j, A (e i) (e j) = A i j) :
    A.toEuclideanLin.comp (Query.linearLift e).toLinearMap =
      (Query.linearLift e).toLinearMap.comp A.toEuclideanLin := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.comp_apply]
  change A.toEuclideanLin (Query.linearLift e (EuclideanSpace.single j 1)) =
    Query.linearLift e (A.toEuclideanLin (EuclideanSpace.single j 1))
  rw [Query.linearLift_single]
  ext i
  have hi := Query.linearLift_apply e
    (A.toEuclideanLin (EuclideanSpace.single j 1)) (e.symm i)
  have hei : e (e.symm i) = i := e.apply_symm_apply i
  rw [hei] at hi
  rw [hi]
  change Matrix.mulVec A (Pi.single (e j) 1) i =
    Matrix.mulVec A (Pi.single j 1) (e.symm i)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simpa only [hei, Matrix.col_apply] using h (e.symm i) j

variable {N : ℕ}

/-- Relabel input by `α` and output by `β`: the manuscript's `β π α⁻¹`.
`Equiv.trans` applies its left operand first. -/
def relabelPerm (α β : Perm N) : Equiv.Perm (Perm N) where
  toFun π := (α.symm.trans π).trans β
  invFun π := (α.trans π).trans β.symm
  left_inv := by
    intro π
    ext x
    simp
  right_inv := by
    intro π
    ext x
    simp

@[simp] theorem relabelPerm_apply (α β π : Perm N) :
    relabelPerm α β π = (α.symm.trans π).trans β := rfl

/-- Actual unitary relabeling on the finite complex permutation-register space. -/
def relabelOperator (α β : Perm N) :
    EuclideanSpace ℂ (Perm N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Perm N) :=
  Query.linearLift (relabelPerm α β)

@[simp] theorem relabelOperator_single (α β π : Perm N) (z : ℂ) :
    relabelOperator α β (EuclideanSpace.single π z) =
      EuclideanSpace.single ((α.symm.trans π).trans β) z :=
  Query.linearLift_single (relabelPerm α β) π z

theorem gramMatrix_commutes (t : ℕ) (α β : Perm N) :
    (gramMatrix N t).toEuclideanLin.comp (relabelOperator α β).toLinearMap =
      (relabelOperator α β).toLinearMap.comp (gramMatrix N t).toEuclideanLin := by
  apply matrix_commutes_of_relabel
  intro π σ
  exact gramMatrix_relabel t π σ α.symm β

/-- The operator assertion following Appendix A's central-kernel formula:
`T T†` commutes with every simultaneous input/output relabeling. -/
theorem T_adjoint_commutes (t : ℕ) (α β : Perm N) :
    ((T N t).comp (T N t).adjoint).comp (relabelOperator α β).toLinearMap =
      (relabelOperator α β).toLinearMap.comp ((T N t).comp (T N t).adjoint) := by
  rw [← gramMatrix_operator]
  exact gramMatrix_commutes t α β

end QuantumOracle.KernelEquivariance
