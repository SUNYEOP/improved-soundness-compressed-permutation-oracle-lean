import QuantumOracle.Model.ExactCoherentQuery
import QuantumOracle.Model.CompressedSupport

/-!
# Actual compressed queries on the shared coherent workspace

Ordinary queries retain the marker as a spectator. Marked queries use the
actual marked compressed oracle. Enable, direction and point are coherent
registers, and the workspace agrees exactly with `ExactCoherentQuery.Args`.
-/

noncomputable section

set_option maxRecDepth 4096

namespace QuantumOracle.CompressedCoherentQuery

open BasisLookup ExactCoherentQuery BlockSupport

variable {N w : ℕ}

/-- The ordinary compressed query, with its unused marker register retained. -/
def ordinaryWithMarker (encode : Encoding N w) (inverse : Bool) (x : Fin N) :
    State (Bool × Bits w) N ≃ₗᵢ[ℂ] State (Bool × Bits w) N :=
  let R := Query.linearLift (Equiv.prodAssoc Bool (Bits w) (Database N))
  R.trans ((BlockOperator.onRight Bool
    (if inverse then CompressedQuery.inverseOrdinary encode x
      else CompressedQuery.ordinary encode x)).trans R.symm)

@[simp] theorem ordinaryWithMarker_apply (encode : Encoding N w)
    (inverse : Bool) (x : Fin N) (ψ : State (Bool × Bits w) N)
    (marker : Bool) (z : Bits w) (I : Database N) :
    ordinaryWithMarker encode inverse x ψ ((marker, z), I) =
      (if inverse then CompressedQuery.inverseOrdinary encode x
        else CompressedQuery.ordinary encode x)
        (WithLp.toLp 2 (fun p => ψ ((marker, p.1), p.2))) (z, I) := rfl


/-- A fixed direction and point, on the common marked-answer workspace. -/
def branch (encode : Encoding N w) (marked inverse : Bool) (x : Fin N) :
    State (Bool × Bits w) N ≃ₗᵢ[ℂ] State (Bool × Bits w) N :=
  if marked then
    if inverse then CompressedQuery.inverseMarked encode x
    else CompressedQuery.marked encode x
  else ordinaryWithMarker encode inverse x

theorem branch_supported (encode : Encoding N w) (marked inverse : Bool)
    (x : Fin N) {t : ℕ} {ψ : State (Bool × Bits w) N}
    (hψ : Supported t ψ) : Supported (t + 1) (branch encode marked inverse x ψ) := by
  cases marked
  · rintro ⟨marker, z⟩ I hI
    change ordinaryWithMarker encode inverse x ψ ((marker, z), I) = 0
    rw [ordinaryWithMarker_apply]
    have hs : Supported t
        (WithLp.toLp 2 (fun p : Bits w × Database N => ψ ((marker, p.1), p.2))) := by
      intro y J hJ
      exact hψ (marker, y) J hJ
    cases inverse
    · exact CompressedSupport.ordinary_supported encode x hs z I hI
    · exact CompressedSupport.inverseOrdinary_supported encode x hs z I hI
  · cases inverse
    · exact CompressedSupport.marked_supported encode x hψ
    · exact CompressedSupport.inverseMarked_supported encode x hψ


/-- Regroup the unchanged controls independently of the answer/database block. -/
def controlsEquiv :
    (Args N w × Database N) ≃
      ((Bool × (Bool × Fin N)) × ((Bool × Bits w) × Database N)) where
  toFun p := ((p.1.1, p.1.2.1), (p.1.2.2, p.2))
  invFun p := ((p.1.1, (p.1.2, p.2.1)), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual controlled compressed oracle on precisely the exact query workspace. -/
def query (encode : Encoding N w) (marked : Bool) :
    State (Args N w) N ≃ₗᵢ[ℂ] State (Args N w) N :=
  let R := Query.linearLift (controlsEquiv (N := N) (w := w))
  R.trans ((BlockOperator.family (fun c : Bool × (Bool × Fin N) =>
    if c.1 then branch encode marked c.2.1 c.2.2
    else LinearIsometryEquiv.refl ℂ _)).trans R.symm)

/-- Fix only the unchanged coherent controls. -/
def markedSlice (ψ : State (Args N w) N) (enable inverse : Bool) (x : Fin N) :
    State (Bool × Bits w) N :=
  WithLp.toLp 2 (fun p => ψ ((enable, ((inverse, x), p.1)), p.2))

@[simp] theorem query_apply (encode : Encoding N w) (marked : Bool)
    (ψ : State (Args N w) N) (enable inverse : Bool) (x : Fin N)
    (z : Bool × Bits w) (I : Database N) :
    query encode marked ψ ((enable, ((inverse, x), z)), I) =
      (if enable then branch encode marked inverse x
        else LinearIsometryEquiv.refl ℂ _)
        (markedSlice ψ enable inverse x) (z, I) := rfl

theorem markedSlice_query_enabled (encode : Encoding N w) (marked inverse : Bool)
    (x : Fin N) (ψ : State (Args N w) N) :
    markedSlice (query encode marked ψ) true inverse x =
      branch encode marked inverse x (markedSlice ψ true inverse x) := by
  ext ⟨z, I⟩
  rfl

theorem markedSlice_query_disabled (encode : Encoding N w) (marked inverse : Bool)
    (x : Fin N) (ψ : State (Args N w) N) :
    markedSlice (query encode marked ψ) false inverse x =
      markedSlice ψ false inverse x := by
  ext ⟨z, I⟩
  rfl

/-- The enabled marked forward branch is the original concrete `pC P pC`. -/
theorem markedSlice_query_forward (encode : Encoding N w) (x : Fin N)
    (ψ : State (Args N w) N) :
    markedSlice (query encode true ψ) true false x =
      CompressedQuery.marked encode x (markedSlice ψ true false x) := by
  exact markedSlice_query_enabled encode true false x ψ

/-- The enabled marked inverse branch is the actual flip-conjugated query. -/
theorem markedSlice_query_inverse (encode : Encoding N w) (x : Fin N)
    (ψ : State (Args N w) N) :
    markedSlice (query encode true ψ) true true x =
      CompressedQuery.inverseMarked encode x (markedSlice ψ true true x) := by
  exact markedSlice_query_enabled encode true true x ψ

/-- Fixing the spectator marker gives the original ordinary answer workspace. -/
def ordinarySlice (ψ : State (Args N w) N)
    (enable inverse : Bool) (x : Fin N) (marker : Bool) : State (Bits w) N :=
  WithLp.toLp 2 (fun p => ψ ((enable, ((inverse, x), (marker, p.1))), p.2))

theorem ordinarySlice_query_enabled (encode : Encoding N w) (inverse : Bool)
    (x : Fin N) (marker : Bool) (ψ : State (Args N w) N) :
    ordinarySlice (query encode false ψ) true inverse x marker =
      (if inverse then CompressedQuery.inverseOrdinary encode x
        else CompressedQuery.ordinary encode x)
        (ordinarySlice ψ true inverse x marker) := by
  ext ⟨z, I⟩
  rfl

theorem query_supported (encode : Encoding N w) (marked : Bool)
    {t : ℕ} {ψ : State (Args N w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (query encode marked ψ) := by
  rintro ⟨enable, ⟨⟨inverse, x⟩, z⟩⟩ I hI
  rw [query_apply]
  have hs : Supported t (markedSlice ψ enable inverse x) := by
    intro y J hJ
    exact hψ (enable, ((inverse, x), y)) J hJ
  cases enable
  · exact supported_mono (Nat.le_succ t) hs z I hI
  · exact branch_supported encode marked inverse x hs z I hI

theorem query_isometry (encode : Encoding N w) (marked : Bool) :
    Isometry (query encode marked) := (query encode marked).isometry

theorem query_norm (encode : Encoding N w) (marked : Bool)
    (ψ : State (Args N w) N) : ‖query encode marked ψ‖ = ‖ψ‖ :=
  (query encode marked).norm_map ψ

/-- An arbitrary finite auxiliary register is retained coherently. -/
def liftedQuery (Aux : Type*) [Fintype Aux] (encode : Encoding N w) (marked : Bool) :
    State (Aux × Args N w) N ≃ₗᵢ[ℂ] State (Aux × Args N w) N :=
  let R := Query.linearLift (Equiv.prodAssoc Aux (Args N w) (Database N))
  R.trans ((BlockOperator.onRight Aux (query encode marked)).trans R.symm)

@[simp] theorem liftedQuery_apply {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) (ψ : State (Aux × Args N w) N)
    (a : Aux) (args : Args N w) (I : Database N) :
    liftedQuery Aux encode marked ψ ((a, args), I) =
      query encode marked (WithLp.toLp 2 (fun p => ψ ((a, p.1), p.2))) (args, I) := rfl

theorem slice_liftedQuery {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) (ψ : State (Aux × Args N w) N) (a : Aux) :
    BlockSupport.slice (liftedQuery Aux encode marked ψ) a =
      query encode marked (BlockSupport.slice ψ a) := by
  ext ⟨args, I⟩
  rfl


theorem liftedQuery_supported {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) {t : ℕ}
    {ψ : State (Aux × Args N w) N} (hψ : Supported t ψ) :
    Supported (t + 1) (liftedQuery Aux encode marked ψ) := by
  rintro ⟨a, args⟩ I hI
  rw [liftedQuery_apply]
  apply query_supported encode marked ?_ args I hI
  intro b J hJ
  exact hψ (a, b) J hJ

theorem liftedQuery_isometry (Aux : Type*) [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) :
    Isometry (liftedQuery Aux encode marked) := (liftedQuery Aux encode marked).isometry

theorem liftedQuery_norm {Aux : Type*} [Fintype Aux]
    (encode : Encoding N w) (marked : Bool) (ψ : State (Aux × Args N w) N) :
    ‖liftedQuery Aux encode marked ψ‖ = ‖ψ‖ := (liftedQuery Aux encode marked).norm_map ψ

-- Keep nested finite-coordinate transports opaque in downstream executions.
attribute [irreducible] ordinaryWithMarker branch query liftedQuery


end QuantumOracle.CompressedCoherentQuery
