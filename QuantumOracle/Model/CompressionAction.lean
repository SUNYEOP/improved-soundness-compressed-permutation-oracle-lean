import QuantumOracle.Model.Compression

/-!
# The action of actual compression on database basis states

The local swap is embedded in the physical database Hilbert space. This proves
the unconditional basis action of the global `pC_x`, including the normalized
sum of all fresh one-edge extensions.
-/

noncomputable section

namespace QuantumOracle.Compression

open CompressionIndex
open scoped BigOperators InnerProductSpace

variable {N : ℕ}

private theorem sum_apply {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (a : α) : (∑ i, v i) a = ∑ i, v i a :=
  map_sum (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : α => ℂ) a) v Finset.univ

/-- Embed one orthogonal compression block into the actual database space. -/
def embedBlock (x : Fin N) (J : Base x)
    (v : EuclideanSpace ℂ (Option (Fresh J.val))) : State N := by
  classical
  exact (reindex x).symm
    ((LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)).symm
      (WithLp.toLp 2 (Pi.single J v)))

@[simp] theorem coordinates_embedBlock_self (x : Fin N) (J : Base x)
    (v : EuclideanSpace ℂ (Option (Fresh J.val))) :
    coordinates x (embedBlock x J v) J = v := by
  classical
  unfold coordinates embedBlock
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext o
  simp [BlockOperator.restrict, Sigma.uncurry]

@[simp] theorem coordinates_embedBlock_other (x : Fin N) (J K : Base x)
    (v : EuclideanSpace ℂ (Option (Fresh J.val))) (h : K ≠ J) :
    coordinates x (embedBlock x J v) K = 0 := by
  classical
  unfold coordinates embedBlock
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext o
  simp [BlockOperator.restrict, Sigma.uncurry, Pi.single_eq_of_ne h]

/-- Equality can be checked in every physical compression block. -/
theorem state_ext_coordinates (x : Fin N) {ψ φ : State N}
    (h : ∀ J, coordinates x ψ J = coordinates x φ J) : ψ = φ := by
  ext I
  obtain ⟨⟨J, o⟩, rfl⟩ := decode_surjective x I
  exact congrArg (fun v : EuclideanSpace ℂ (Option (Fresh J.val)) => v o) (h J)

/-- The global compression intertwines the actual embedding and local swap. -/
theorem pC_embedBlock (x : Fin N) (J : Base x)
    (v : EuclideanSpace ℂ (Option (Fresh J.val))) :
    pC x (embedBlock x J v) =
      embedBlock x J (CompressionBlock.compression (Fresh J.val) v) := by
  classical
  apply state_ext_coordinates x
  intro K
  by_cases h : K = J
  · subst K
    simp
  · simp [coordinates_embedBlock_other, h]

/-- A physical database basis vector. -/
def ket (I : Database N) : State N := by
  classical
  exact EuclideanSpace.single I 1

theorem embedBlock_single (x : Fin N) (J : Base x)
    (o : Option (Fresh J.val)) (a : ℂ) :
    embedBlock x J (EuclideanSpace.single o a) =
      EuclideanSpace.single (decode x ⟨J, o⟩) a := by
  classical
  apply state_ext_coordinates x
  intro K
  by_cases h : K = J
  · subst K
    rw [coordinates_embedBlock_self]
    ext p
    simp [(decode_injective x).eq_iff]
  · rw [coordinates_embedBlock_other x J K _ h]
    ext p
    have hdecode : decode x ⟨K, p⟩ ≠ decode x ⟨J, o⟩ := by
      intro heq
      exact h (congrArg Sigma.fst (decode_injective x heq))
    simp [hdecode]

@[simp] theorem embedBlock_empty (x : Fin N) (J : Base x) :
    embedBlock x J (UniformState.emptyKet (Fresh J.val)) = ket J.val := by
  have hlocal : UniformState.emptyKet (Fresh J.val) = EuclideanSpace.single none 1 := by
    ext o
    cases o <;> simp
  rw [hlocal, embedBlock_single]
  ext I
  simp [ket]

@[simp] theorem coordinates_sum {ι : Type*} [Fintype ι]
    (x : Fin N) (v : ι → State N) (J : Base x) :
    coordinates x (∑ i, v i) J = ∑ i, coordinates x (v i) J := by
  ext o
  simp [sum_apply]

theorem embedBlock_sum {ι : Type*} [Fintype ι] (x : Fin N) (J : Base x)
    (v : ι → EuclideanSpace ℂ (Option (Fresh J.val))) :
    embedBlock x J (∑ i, v i) = ∑ i, embedBlock x J (v i) := by
  classical
  apply state_ext_coordinates x
  intro K
  by_cases h : K = J
  · subst K
    simp
  · simp [coordinates_embedBlock_other, h]

/-- The actual uniform superposition of the fresh extensions of `J`. -/
def plusState (x : Fin N) (J : Base x) : State N :=
  embedBlock x J (UniformState.extensionUniform (Fresh J.val))

/-- In database coordinates this is exactly the normalized fresh extension sum. -/
theorem plusState_eq_sum (x : Fin N) (J : Base x) :
    plusState x J = ∑ y : Fresh J.val,
      EuclideanSpace.single (J.val.set x y.val) (UniformState.amplitude (Fresh J.val) : ℂ) := by
  have hlocal : UniformState.extensionUniform (Fresh J.val) =
      ∑ y : Fresh J.val, EuclideanSpace.single (some y)
        (UniformState.amplitude (Fresh J.val) : ℂ) := by
    ext o
    cases o <;> simp [sum_apply]
  unfold plusState
  rw [hlocal, embedBlock_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact embedBlock_single x J (some y) _

/-- The displayed normalized ket sum from the manuscript. -/
theorem plusState_eq_smul_sum (x : Fin N) (J : Base x) :
    plusState x J = (UniformState.amplitude (Fresh J.val) : ℂ) •
      ∑ y : Fresh J.val, ket (J.val.set x y.val) := by
  classical
  rw [plusState_eq_sum]
  ext I
  simp only [PiLp.smul_apply, sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [ket, mul_ite]

/-- The normalization coefficient uses the actual number `N - |J|` of fresh outputs. -/
theorem plusState_eq_manuscript (x : Fin N) (J : Base x) :
    plusState x J = ((Real.sqrt ((N - J.val.size : ℕ) : ℝ))⁻¹ : ℂ) •
      ∑ y : Fresh J.val, ket (J.val.set x y.val) := by
  rw [plusState_eq_smul_sum, UniformState.amplitude, card_fresh]
  simp only [Complex.ofReal_inv]

/-- Actual compression sends the basis state `|J⟩` to `|+_{J,x}⟩`. -/
@[simp] theorem pC_ket_base (x : Fin N) (J : Base x) :
    pC x (ket J.val) = plusState x J := by
  letI := fresh_nonempty J
  rw [← embedBlock_empty x J, pC_embedBlock, CompressionBlock.compression_empty]
  rfl

/-- Actual compression sends `|+_{J,x}⟩` back to `|J⟩`. -/
@[simp] theorem pC_plusState (x : Fin N) (J : Base x) :
    pC x (plusState x J) = ket J.val := by
  rw [← pC_ket_base x J, pC_involutive]

@[simp] theorem plusState_norm (x : Fin N) (J : Base x) : ‖plusState x J‖ = 1 := by
  rw [← pC_ket_base x J, (pC x).norm_map]
  simp [ket]

/-- Every vector in the common orthogonal complement of the exchanged pair
is fixed, after embedding in the actual database space. -/
theorem pC_embedBlock_fixed (x : Fin N) (J : Base x)
    (v : EuclideanSpace ℂ (Option (Fresh J.val)))
    (he : ⟪UniformState.emptyKet (Fresh J.val), v⟫_ℂ = 0)
    (hu : ⟪UniformState.extensionUniform (Fresh J.val), v⟫_ℂ = 0) :
    pC x (embedBlock x J v) = embedBlock x J v := by
  rw [pC_embedBlock, CompressionBlock.compression_fixed _ _ he hu]

end QuantumOracle.Compression

