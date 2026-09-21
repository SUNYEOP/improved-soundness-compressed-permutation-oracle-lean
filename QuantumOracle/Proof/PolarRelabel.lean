import QuantumOracle.Proof.RelabelSymmetry
import QuantumOracle.Model.PolarEmbedding
import QuantumOracle.Proof.PolarUnitary

/-!
# Full input/output relabeling symmetry of the actual polar embedding

These are the concrete basis permutations on actual permutations and partial
injections. Their unitarity and the raw intertwining theorem supply all inputs
to polar normalization; no equivariance premise is supplied by the caller.
-/

noncomputable section

namespace QuantumOracle.PolarRelabel

open PermutationExtensions KernelEquivariance

variable {N : ℕ}

theorem candidate_intertwines_linearMap (α β : Perm N) :
    (PolarEmbedding.candidate N).toLinearMap.comp (relabelOperator α β).toLinearEquiv.toLinearMap =
      (DatabaseRelabel.operator α β).toLinearEquiv.toLinearMap.comp
        (PolarEmbedding.candidate N).toLinearMap := by
  apply PolarUnitary.isometry_intertwines (PolarEmbedding.matrix N)
    (PolarEmbedding.matrix_mulVec_injective N) (relabelOperator α β)
    (DatabaseRelabel.operator α β)
  rw [PolarEmbedding.matrix_operator]
  apply LinearMap.ext
  intro h
  exact RelabelSymmetry.total_intertwines α β h

/-- Relabeling actual inputs and outputs commutes with the normalized embedding. -/
theorem candidate_intertwines (α β : Perm N) (h : EuclideanSpace ℂ (Perm N)) :
    PolarEmbedding.candidate N (relabelOperator α β h) =
      DatabaseRelabel.operator α β (PolarEmbedding.candidate N h) :=
  LinearMap.congr_fun (candidate_intertwines_linearMap α β) h

theorem candidate_apply_relabel (α β : Perm N)
    (h : EuclideanSpace ℂ (Perm N)) (I : Database N) :
    PolarEmbedding.candidate N (relabelOperator α β h) (DatabaseRelabel.relabel α β I) =
      PolarEmbedding.candidate N h I := by
  rw [candidate_intertwines, DatabaseRelabel.operator_apply_relabel]

/-- The relabeled actual image has the same physical cancellation at every input. -/
theorem candidate_cancels_relabel (α β : Perm N) (x : Fin N)
    (h : EuclideanSpace ℂ (Perm N)) :
    CompressionCancellation.Cancels x
      (DatabaseRelabel.operator α β (PolarEmbedding.candidate N h)) := by
  rw [← candidate_intertwines]
  exact PolarEmbedding.candidate_cancels x _

end QuantumOracle.PolarRelabel
