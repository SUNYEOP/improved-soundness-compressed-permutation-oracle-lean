import QuantumOracle.Model.KnowledgeSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal layers of the actual knowledge filtration

These are the successive orthogonal differences of the concrete spaces `K`.
The decomposition uses only finite-dimensional Hilbert-space geometry; no
identification with symmetric-group representations or spectrum is assumed.
-/

noncomputable section

namespace QuantumOracle.HarmonicLayers

open PermutationExtensions KnowledgeSpace
open scoped InnerProductSpace BigOperators

/-- Degree zero is the uniform line; each later degree is the orthogonal
increment of the actual consistent-state filtration. -/
def H (N : ℕ) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Perm N))
  | 0 => K N 0
  | t + 1 => K N (t + 1) ⊓ (K N t)ᗮ

@[simp] theorem H_zero (N : ℕ) : H N 0 = K N 0 := rfl

@[simp] theorem H_succ (N t : ℕ) :
    H N (t + 1) = K N (t + 1) ⊓ (K N t)ᗮ := rfl

theorem H_le_K (N t : ℕ) : H N t ≤ K N t := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact inf_le_left

theorem H_succ_le_orthogonal (N t : ℕ) : H N (t + 1) ≤ (K N t)ᗮ :=
  inf_le_right

/-- Each valid filtration step splits as the previous level plus its
orthogonal increment. -/
theorem K_succ_eq_sup {N t : ℕ} (ht : t < N) :
    K N (t + 1) = K N t ⊔ H N (t + 1) := by
  rw [H_succ, inf_comm]
  exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_succ ht)).symm

/-- A higher valid layer is perpendicular to every lower layer. -/
theorem orthogonal_of_lt {N s t : ℕ} (hst : s < t) (ht : t ≤ N) :
    H N t ≤ (H N s)ᗮ := by
  cases t with
  | zero => omega
  | succ t =>
    exact (H_succ_le_orthogonal N t).trans
      (Submodule.orthogonal_le ((H_le_K N s).trans
        (KnowledgeSpace.mono (Nat.le_of_lt_succ hst) (by omega))))

theorem inner_eq_zero_of_lt {N s t : ℕ} (hst : s < t) (ht : t ≤ N)
    {v z : EuclideanSpace ℂ (Perm N)} (hv : v ∈ H N s) (hz : z ∈ H N t) :
    inner ℂ v z = 0 :=
  Submodule.inner_right_of_mem_orthogonal hv (orthogonal_of_lt hst ht hz)

/-- Every valid knowledge space is the sum of its actual orthogonal layers. -/
theorem K_eq_iSup {N t : ℕ} (ht : t ≤ N) :
    K N t = ⨆ i : Fin (t + 1), H N i.val := by
  apply le_antisymm
  · induction t with
    | zero =>
      exact le_iSup (fun i : Fin 1 => H N i.val) 0
    | succ t ih =>
      rw [K_succ_eq_sup (by omega)]
      refine sup_le ?_ ?_
      · exact (ih (by omega)).trans
          (iSup_le fun i => le_iSup_of_le i.castSucc le_rfl)
      · exact le_iSup_of_le (Fin.last (t + 1)) le_rfl
  · refine iSup_le fun i => ?_
    exact (H_le_K N i.val).trans
      (KnowledgeSpace.mono (Nat.le_of_lt_succ i.isLt) ht)

/-- The finitely many layers exhaust the full exact permutation register. -/
theorem iSup_eq_top (N : ℕ) :
    (⨆ i : Fin (N + 1), H N i.val) = ⊤ := by
  rw [← K_eq_iSup (le_refl N), full_eq_top]

theorem H_eq_bot_of_gt {N t : ℕ} (ht : N < t) : H N t = ⊥ := by
  apply bot_unique
  exact (H_le_K N t).trans (le_of_eq (eq_bot_of_gt ht))

attribute [local irreducible] H KnowledgeSpace.K

local instance layerInnerProductSpace (N t : ℕ) :
    (i : Fin (t + 1)) → InnerProductSpace ℂ ↥(H N i.val) := fun _ => inferInstance

/-- The inclusions of the degree spaces form a genuine orthogonal family. -/
theorem orthogonalFamily {N t : ℕ} (ht : t ≤ N) :
    OrthogonalFamily ℂ (fun i : Fin (t + 1) => ↥(H N i.val))
      (fun i => (H N i.val).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Submodule.IsOrtho.symm
      (orthogonal_of_lt hij ((Nat.le_of_lt_succ j.isLt).trans ht))
  · exact orthogonal_of_lt hji ((Nat.le_of_lt_succ i.isLt).trans ht)

/-- The orthogonal projections reconstruct every vector of a knowledge level. -/
theorem sum_projection_of_mem {N t : ℕ} (ht : t ≤ N)
    (v : EuclideanSpace ℂ (Perm N)) (hv : v ∈ K N t) :
    (∑ i : Fin (t + 1), (H N i.val).starProjection v) = v := by
  apply (orthogonalFamily ht).sum_projection_of_mem_iSup
  rwa [← K_eq_iSup ht]

/-- Every exact hidden-register vector has a concrete orthogonal degree decomposition. -/
theorem sum_projection (N : ℕ) (v : EuclideanSpace ℂ (Perm N)) :
    (∑ i : Fin (N + 1), (H N i.val).starProjection v) = v := by
  apply sum_projection_of_mem (le_refl N)
  rw [full_eq_top]
  exact Submodule.mem_top

end QuantumOracle.HarmonicLayers
