import QuantumOracle.Proof.KernelEquivariance

/-!
# Actual input/output relabeling of partial-injection databases

The edge graph is transported by `(x,y) ↦ (α x, β y)`. This is the database
counterpart of the actual permutation relabeling `π ↦ β π α⁻¹`.
-/

noncomputable section

namespace QuantumOracle.DatabaseRelabel

open PermutationExtensions

variable {N : ℕ}

/-- Transport every actual edge by the input and output bijections. -/
def relabel (α β : Perm N) (I : Database N) : Database N where
  edges := I.edges.map (Equiv.prodCongr α β).toEmbedding
  functional := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hf
    exact congrArg β (I.functional ha hb (α.injective h))
  injective := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hf
    exact congrArg α (I.injective ha hb (β.injective h))

@[simp] theorem mem_relabel (α β : Perm N) (I : Database N) (x y : Fin N) :
    (x, y) ∈ (relabel α β I).edges ↔ (α.symm x, β.symm y) ∈ I.edges :=
  Finset.mem_map_equiv

@[simp] theorem relabel_size (α β : Perm N) (I : Database N) :
    (relabel α β I).size = I.size := by
  rw [Database.size_eq_card_edges, Database.size_eq_card_edges]
  exact Finset.card_map _

@[simp] theorem relabel_symm_relabel (α β : Perm N) (I : Database N) :
    relabel α.symm β.symm (relabel α β I) = I := by
  ext ⟨x, y⟩
  simp only [mem_relabel, Equiv.symm_symm, Equiv.symm_apply_apply]

@[simp] theorem relabel_relabel_symm (α β : Perm N) (I : Database N) :
    relabel α β (relabel α.symm β.symm I) = I := by
  simpa only [Equiv.symm_symm] using relabel_symm_relabel α.symm β.symm I

/-- Actual basis permutation of all databases, with the inverse relabeling. -/
def equiv (α β : Perm N) : Equiv.Perm (Database N) where
  toFun := relabel α β
  invFun := relabel α.symm β.symm
  left_inv := relabel_symm_relabel α β
  right_inv := relabel_relabel_symm α β

/-- The actual database-register relabeling, extended linearly and isometrically. -/
def operator (α β : Perm N) :
    EuclideanSpace ℂ (Database N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Database N) :=
  Query.linearLift (equiv α β)

@[simp] theorem operator_apply (α β : Perm N)
    (ψ : EuclideanSpace ℂ (Database N)) (I : Database N) :
    operator α β ψ I = ψ (relabel α.symm β.symm I) := rfl

@[simp] theorem operator_apply_relabel (α β : Perm N)
    (ψ : EuclideanSpace ℂ (Database N)) (I : Database N) :
    operator α β ψ (relabel α β I) = ψ I := by
  rw [operator_apply, relabel_symm_relabel]

/-- Relabeling preserves precisely the actual extension constraints. -/
theorem extends_relabel_iff (α β : Perm N) (I : Database N) (π : Perm N) :
    Extends (relabel α β I) (KernelEquivariance.relabelPerm α β π) ↔ Extends I π := by
  constructor
  · intro h x y hxy
    have he := h (α x) (β y) (by simpa only [mem_relabel, Equiv.symm_apply_apply] using hxy)
    apply β.injective
    simpa only [KernelEquivariance.relabelPerm_apply, Equiv.trans_apply,
      Equiv.symm_apply_apply] using he
  · intro h x y hxy
    have he := h (α.symm x) (β.symm y) ((mem_relabel α β I x y).mp hxy)
    change β (π (α.symm x)) = y
    rw [he, Equiv.apply_symm_apply]

/-- Simultaneously relabeling a database and a permutation preserves its amplitude. -/
theorem vector_relabel_apply (α β : Perm N) (I : Database N) (π : Perm N) :
    ConsistentState.vector (relabel α β I) (KernelEquivariance.relabelPerm α β π) =
      ConsistentState.vector I π := by
  classical
  simp only [ConsistentState.vector_apply, extends_relabel_iff,
    ConsistentState.amplitude, relabel_size]

end QuantumOracle.DatabaseRelabel
