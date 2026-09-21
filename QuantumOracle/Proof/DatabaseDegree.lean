import QuantumOracle.Model.RawHarmonic

/-!
# Physical database-size subspaces and their projections

These are diagonal coordinate projections on the actual database register.
They introduce no assumptions about the harmonic or polar embedding.
-/

noncomputable section

namespace QuantumOracle.DatabaseDegree

open Compression
open scoped InnerProductSpace

/-- Amplitudes vanish outside databases of exactly the specified size. -/
def exactLevel (N t : ℕ) : Submodule ℂ (State N) where
  carrier := {ψ | ∀ I : Database N, I.size ≠ t → ψ I = 0}
  zero_mem' := by simp
  add_mem' := by
    intro ψ φ hψ hφ I hI
    simp [PiLp.add_apply, hψ I hI, hφ I hI]
  smul_mem' := by
    intro a ψ hψ I hI
    simp [PiLp.smul_apply, hψ I hI]

/-- Actual diagonal projection onto one database size. -/
def project (N t : ℕ) : State N →ₗ[ℂ] State N where
  toFun ψ := WithLp.toLp 2 (fun I => if I.size = t then ψ I else 0)
  map_add' ψ φ := by
    classical
    ext I
    by_cases hI : I.size = t <;> simp [hI]
  map_smul' a ψ := by
    classical
    ext I
    by_cases hI : I.size = t <;> simp [hI]

@[simp] theorem project_apply (N t : ℕ) (ψ : State N) (I : Database N) :
    project N t ψ I = if I.size = t then ψ I else 0 := rfl

theorem project_mem (N t : ℕ) (ψ : State N) : project N t ψ ∈ exactLevel N t := by
  intro I hI
  simp [hI]

theorem project_eq_self_iff (N t : ℕ) (ψ : State N) :
    project N t ψ = ψ ↔ ψ ∈ exactLevel N t := by
  constructor
  · intro h
    rw [← h]
    exact project_mem N t ψ
  · intro h
    ext I
    by_cases hI : I.size = t
    · simp [hI]
    · simp [hI, h I hI]

theorem project_isSymmetric (N t : ℕ) : (project N t).IsSymmetric := by
  intro ψ φ
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : I.size = t <;> simp [hI]

@[simp] theorem project_project (N t : ℕ) (ψ : State N) :
    project N t (project N t ψ) = project N t ψ :=
  (project_eq_self_iff N t _).mpr (project_mem N t ψ)

/-- Raw adjoint images already lie in their exact physical size. -/
theorem raw_mem (N t : ℕ) (h : EuclideanSpace ℂ (PermutationExtensions.Perm N)) :
    RawHarmonic.raw N t h ∈ exactLevel N t :=
  fun I hI => RawHarmonic.raw_apply_of_ne N t h I hI

@[simp] theorem project_raw_self (N t : ℕ)
    (h : EuclideanSpace ℂ (PermutationExtensions.Perm N)) :
    project N t (RawHarmonic.raw N t h) = RawHarmonic.raw N t h :=
  (project_eq_self_iff N t _).mpr (raw_mem N t h)

theorem project_raw_of_ne (N s t : ℕ) (hst : s ≠ t)
    (h : EuclideanSpace ℂ (PermutationExtensions.Perm N)) :
    project N s (RawHarmonic.raw N t h) = 0 := by
  ext I
  by_cases hI : I.size = s
  · rw [project_apply, if_pos hI,
      RawHarmonic.raw_apply_of_ne N t h I (fun ht => hst (hI.symm.trans ht))]
    rfl
  · simp [hI]

end QuantumOracle.DatabaseDegree
