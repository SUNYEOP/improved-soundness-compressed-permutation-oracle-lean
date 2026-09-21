import QuantumOracle.Proof.SpechtLayers

/-!
# Actual full Specht isotypic blocks of the regular permutation register

`SpechtGram.space` is one concrete irreducible left ideal. Here `component`
contains every isomorphic left submodule of the regular group algebra, and
`space` transports that whole isotypic component to the actual Hilbert space.
The actual Gram scalar extends to all these copies and the blocks span the
register. No Hilbert orthogonality or residual branching statement is claimed
by the algebraic spanning result.
-/

noncomputable section

namespace QuantumOracle.SpechtIsotypic

open PermutationExtensions GramConvolution SpechtCharacter

/-- The full regular left-isotypic component of the actual constructed Specht module. -/
def component (N : ℕ) (la : Nat.Partition N) :
    Submodule (GroupAlgebra N) (GroupAlgebra N) :=
  isotypicComponent (GroupAlgebra N) (GroupAlgebra N) (SpechtFoundation.specht N la)

/-- The full isotypic block with its original permutation coefficients. -/
def space (N : ℕ) (la : Nat.Partition N) :
    Submodule ℂ (EuclideanSpace ℂ (Perm N)) :=
  ((component N la).restrictScalars ℂ).comap (equiv N).toLinearMap

@[simp] theorem mem_space (N : ℕ) (la : Nat.Partition N)
    (h : EuclideanSpace ℂ (Perm N)) :
    h ∈ space N la ↔ equiv N h ∈ component N la := Iff.rfl

theorem specht_le_component (N : ℕ) (la : Nat.Partition N) :
    SpechtFoundation.specht N la ≤ component N la :=
  Submodule.le_isotypicComponent _

theorem spechtSpace_le_space (N : ℕ) (la : Nat.Partition N) :
    SpechtGram.space N la ≤ space N la :=
  fun _ hh => specht_le_component N la hh

/-- The central actual Gram convolution on the entire regular group algebra. -/
def algebraGram (N t : ℕ) : GroupAlgebra N →ₗ[GroupAlgebra N] GroupAlgebra N where
  toFun a := kernel N t * a
  map_add' := fun a b => mul_add _ _ _
  map_smul' := fun a b => by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← mul_assoc, kernel_commutes, mul_assoc]

@[simp] theorem algebraGram_apply (N t : ℕ) (a : GroupAlgebra N) :
    algebraGram N t a = kernel N t * a := rfl

/-- The already computed scalar on the defining Specht module, in module-action form. -/
theorem kernel_smul_specht (N t : ℕ) (la : Nat.Partition N)
    (v : SpechtFoundation.specht N la) :
    kernel N t • v = eigenvalue N t la • v := by
  obtain ⟨c, hc⟩ := SpechtGram.algebraGram_scalar N t la
  rw [← scalar_eq_eigenvalue N t la c hc]
  exact hc v

/-- Module isomorphisms carry the same actual central Gram scalar to every copy. -/
theorem algebraGram_eq_eigenvalue (N t : ℕ) (la : Nat.Partition N)
    {a : GroupAlgebra N} (ha : a ∈ component N la) :
    algebraGram N t a = eigenvalue N t la • a := by
  have hle : component N la ≤
      LinearMap.ker (algebraGram N t - eigenvalue N t la • LinearMap.id) := by
    apply sSup_le
    rintro S ⟨e⟩ a ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    have hm : algebraGram N t a ∈ S := S.smul_mem (kernel N t) ha
    have he : (⟨algebraGram N t a, hm⟩ : S) = eigenvalue N t la • (⟨a, ha⟩ : S) := by
      apply e.injective
      change e (kernel N t • (⟨a, ha⟩ : S)) = e (eigenvalue N t la • (⟨a, ha⟩ : S))
      rw [map_smul]
      exact (kernel_smul_specht N t la _).trans
        (e.toLinearMap.map_smul_of_tower (eigenvalue N t la) (⟨a, ha⟩ : S)).symm
    exact congrArg Subtype.val he
  have hz := hle ha
  change algebraGram N t a - eigenvalue N t la • a = 0 at hz
  exact sub_eq_zero.mp hz

/-- The original extension Gram operator has the proved scalar on the whole block. -/
theorem gram_eq_eigenvalue (N t : ℕ) (la : Nat.Partition N)
    {h : EuclideanSpace ℂ (Perm N)} (hh : h ∈ space N la) :
    GramFiltration.gram N t h = eigenvalue N t la • h := by
  apply (equiv N).injective
  rw [equiv_gram_left, map_smul]
  exact algebraGram_eq_eigenvalue N t la hh

/-- Completeness of the actual constructed Specht modules gives algebraic spanning. -/
theorem iSup_component_eq_top (N : ℕ) : (⨆ la : Nat.Partition N, component N la) = ⊤ := by
  apply top_unique
  rw [← sSup_isotypicComponents (GroupAlgebra N) (GroupAlgebra N)]
  apply sSup_le
  rintro S ⟨V, hV, rfl⟩
  letI := hV
  obtain ⟨la, ⟨e⟩⟩ :=
    RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype N V
  rw [e.isotypicComponent_eq]
  exact le_iSup (component N) la

/-- The full isotypic blocks exhaust the actual regular permutation register. -/
theorem iSup_space_eq_top (N : ℕ) : (⨆ la : Nat.Partition N, space N la) = ⊤ := by
  apply Submodule.map_injective_of_injective (equiv N).injective
  rw [Submodule.map_iSup]
  simp only [space, Submodule.map_comap_eq_of_surjective (equiv N).surjective]
  rw [← Submodule.restrictScalars_iSup, iSup_component_eq_top]
  simp only [Submodule.restrictScalars_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr (equiv N).surjective]

end QuantumOracle.SpechtIsotypic
