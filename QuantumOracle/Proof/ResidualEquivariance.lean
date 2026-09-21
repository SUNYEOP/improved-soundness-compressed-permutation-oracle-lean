import QuantumOracle.Proof.ResidualAdjoint
import QuantumOracle.Proof.KernelEquivariance

/-!
# Actual stabilizer equivariance of answer restriction

The complementary permutation group embeds by fixing the removed point.
Restricting an actual answer sector intertwines both actual input and output
stabilizer actions with the ordinary residual relabeling actions. This provides
the concrete operator identity needed for representation-theoretic branching;
it does not assume or choose a Specht decomposition.
-/

noncomputable section

namespace QuantumOracle.ResidualEquivariance

open PermutationExtensions ResidualPermutation KernelEquivariance

variable {N : ℕ}

/-- Embed the actual residual group as permutations fixing the chosen point. -/
def stabilizerEmbed (x : Fin (N + 1)) : Perm N →* Perm (N + 1) where
  toFun := insert x x
  map_one' := by
    apply Equiv.ext
    intro a
    by_cases ha : a = x
    · subst a
      exact insert_at x x 1
    · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
      exact insert_succAbove x x 1 b
  map_mul' σ τ := by
    apply Equiv.ext
    intro a
    by_cases ha : a = x
    · subst a
      simp only [Equiv.Perm.mul_apply, insert_at]
    · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
      simp only [Equiv.Perm.mul_apply, insert_succAbove]

@[simp] theorem stabilizerEmbed_at (x : Fin (N + 1)) (σ : Perm N) :
    stabilizerEmbed x σ x = x := insert_at x x σ

@[simp] theorem stabilizerEmbed_succAbove (x : Fin (N + 1)) (σ : Perm N) (a : Fin N) :
    stabilizerEmbed x σ (x.succAbove a) = x.succAbove (σ a) := insert_succAbove x x σ a

theorem stabilizerEmbed_injective (x : Fin (N + 1)) :
    Function.Injective (stabilizerEmbed x) := insert_injective x x

/-- The actual embedded group has exactly the full point stabilizer as range. -/
theorem mem_range_stabilizerEmbed (x : Fin (N + 1)) (π : Perm (N + 1)) :
    π ∈ Set.range (stabilizerEmbed x) ↔ π x = x := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact stabilizerEmbed_at x σ
  · intro hπ
    exact ⟨remove x x ⟨π, hπ⟩, insert_remove x x ⟨π, hπ⟩⟩

/-- Inserting a fixed edge respects both stabilizer relabelings on the nose. -/
theorem insert_relabel (x y : Fin (N + 1)) (α β σ : Perm N) :
    insert x y (relabelPerm α β σ) =
      relabelPerm (stabilizerEmbed x α) (stabilizerEmbed y β) (insert x y σ) := by
  apply Equiv.ext
  intro a
  change _ = stabilizerEmbed y β (insert x y σ ((stabilizerEmbed x α).symm a))
  have hinv : (stabilizerEmbed x α).symm = stabilizerEmbed x α.symm :=
    (map_inv (stabilizerEmbed x) α).symm
  rw [hinv]
  by_cases ha : a = x
  · subst a
    simp only [insert_at, stabilizerEmbed_at]
  · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
    simp only [insert_succAbove, stabilizerEmbed_succAbove]
    rfl

/-- The actual answer restriction is equivariant for both point stabilizers,
including every answer and the empty residual domain. -/
theorem restrict_relabel (x y : Fin (N + 1)) (α β : Perm N)
    (h : EuclideanSpace ℂ (Perm (N + 1))) :
    ResidualAdjoint.restrict x y
        (relabelOperator (stabilizerEmbed x α) (stabilizerEmbed y β) h) =
      relabelOperator α β (ResidualAdjoint.restrict x y h) := by
  ext σ
  obtain ⟨τ, rfl⟩ := (relabelPerm α β).surjective σ
  rw [ResidualAdjoint.restrict_apply, insert_relabel]
  rw [show relabelOperator (stabilizerEmbed x α) (stabilizerEmbed y β) h
      (relabelPerm (stabilizerEmbed x α) (stabilizerEmbed y β) (insert x y τ)) =
        h (insert x y τ) from Query.linearLift_apply _ _ _]
  rw [show relabelOperator α β (ResidualAdjoint.restrict x y h) (relabelPerm α β τ) =
      ResidualAdjoint.restrict x y h τ from Query.linearLift_apply _ _ _]
  rfl

theorem restrict_relabel_linearMap (x y : Fin (N + 1)) (α β : Perm N) :
    (ResidualAdjoint.restrict x y).comp
        (relabelOperator (stabilizerEmbed x α) (stabilizerEmbed y β)).toLinearEquiv.toLinearMap =
      (relabelOperator α β).toLinearEquiv.toLinearMap.comp (ResidualAdjoint.restrict x y) := by
  apply LinearMap.ext
  intro h
  exact restrict_relabel x y α β h

end QuantumOracle.ResidualEquivariance
