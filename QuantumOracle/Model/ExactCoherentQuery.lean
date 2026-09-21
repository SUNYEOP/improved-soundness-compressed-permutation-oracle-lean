import QuantumOracle.Model.Query

/-!
# Exact queries with coherent arguments

The input point, forward/inverse direction and query-enable bit all belong to
the query Hilbert space. Ordinary and marked queries share one marker register;
the Boolean parameter chooses whether the enabled branch flips that marker.
The permutation register is read only. All maps are actual basis permutations
and their complex linear isometry lifts.
-/

noncomputable section

namespace QuantumOracle.ExactCoherentQuery

open BasisLookup Query

attribute [local instance] Classical.propDecidable

/-- Enable, direction/point, and marker/output registers. -/
abbrev Args (N w : ℕ) := Bool × ((Bool × Fin N) × (Bool × Bits w))

variable {N w : ℕ}

/-- The reversible answer-register update for an explicitly supplied answer. -/
def answerArgs (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (y : Fin N) : Args N w :=
  (args.1, (args.2.1,
    if args.1 then (Bool.xor args.2.2.1 marked, xor args.2.2.2 (encode y))
    else args.2.2))

@[simp] theorem answerArgs_disabled (encode : Encoding N w) (marked : Bool)
    (inverse : Bool) (x : Fin N) (z : Bool × Bits w) (y : Fin N) :
    answerArgs encode marked (false, ((inverse, x), z)) y =
      (false, ((inverse, x), z)) := rfl

@[simp] theorem answerArgs_enabled (encode : Encoding N w) (marked : Bool)
    (inverse : Bool) (x : Fin N) (z : Bool × Bits w) (y : Fin N) :
    answerArgs encode marked (true, ((inverse, x), z)) y =
      (true, ((inverse, x), (Bool.xor z.1 marked, xor z.2 (encode y)))) := rfl

@[simp] theorem answerArgs_enable (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (y : Fin N) :
    (answerArgs encode marked args y).1 = args.1 := rfl

@[simp] theorem answerArgs_input (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (y : Fin N) :
    (answerArgs encode marked args y).2.1 = args.2.1 := rfl

theorem answerArgs_involutive (encode : Encoding N w) (marked : Bool)
    (y : Fin N) : Function.Involutive (fun args => answerArgs encode marked args y) := by
  rintro ⟨enable, ⟨⟨inverse, x⟩, ⟨marker, z⟩⟩⟩
  cases enable <;> cases marker <;> cases marked <;> simp [answerArgs]

/-- For one fixed permutation, the enable and input registers coherently control
the reversible output update. -/
def argumentBasis (encode : Encoding N w) (marked : Bool)
    (π : Equiv.Perm (Fin N)) : Equiv.Perm (Args N w) :=
  BasisLookup.controlled (Query.indexedBasis fun ix : Bool × Fin N =>
    Equiv.prodCongr (bitXorPerm marked)
      (xorPerm (encode (permutationAnswer ix.1 π ix.2))))

@[simp] theorem argumentBasis_apply (encode : Encoding N w) (marked : Bool)
    (π : Equiv.Perm (Fin N)) (args : Args N w) :
    argumentBasis encode marked π args =
      answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2) := by
  rcases args with ⟨enable, rest⟩
  cases enable <;> rfl

@[simp] theorem argumentBasis_symm_apply (encode : Encoding N w) (marked : Bool)
    (π : Equiv.Perm (Fin N)) (args : Args N w) :
    (argumentBasis encode marked π).symm args =
      answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2) := by
  rcases args with ⟨enable, rest⟩
  cases enable <;> rfl

/-- The concrete permutation-query basis map, with an unchanged oracle register. -/
def queryBasis (encode : Encoding N w) (marked : Bool) :
    Equiv.Perm (Args N w × Equiv.Perm (Fin N)) :=
  Query.registerBasis (argumentBasis encode marked)

@[simp] theorem queryBasis_apply (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (π : Equiv.Perm (Fin N)) :
    queryBasis encode marked (args, π) =
      (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2), π) := by
  change (argumentBasis encode marked π args, π) = _
  rw [argumentBasis_apply]

@[simp] theorem queryBasis_symm_apply (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (π : Equiv.Perm (Fin N)) :
    (queryBasis encode marked).symm (args, π) =
      (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2), π) := by
  change ((argumentBasis encode marked π).symm args, π) = _
  rw [argumentBasis_symm_apply]

theorem queryBasis_involutive (encode : Encoding N w) (marked : Bool) :
    Function.Involutive (queryBasis encode marked) := by
  intro a
  obtain ⟨args, π⟩ := a
  rw [queryBasis_apply, queryBasis_apply]
  change (answerArgs encode marked
      (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2))
      (permutationAnswer args.2.1.1 π args.2.1.2), π) = (args, π)
  exact congrArg (fun a => (a, π))
    (answerArgs_involutive encode marked (permutationAnswer args.2.1.1 π args.2.1.2) args)

/-- Exact ordinary (`marked = false`) and marked (`marked = true`) queries on
the same complete coherent argument space. -/
def query (encode : Encoding N w) (marked : Bool) :
    EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)) :=
  Query.linearLift (queryBasis encode marked)

/-- Coordinates are pulled back by the same answer update, since XOR queries
are involutions. This applies to arbitrary superposed, nonzero answer registers. -/
@[simp] theorem query_apply (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (args : Args N w) (π : Equiv.Perm (Fin N)) :
    query encode marked ψ (args, π) =
      ψ (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2), π) := by
  change ψ ((queryBasis encode marked).symm (args, π)) = _
  rw [queryBasis_symm_apply]

@[simp] theorem query_single (encode : Encoding N w) (marked : Bool)
    (args : Args N w) (π : Equiv.Perm (Fin N)) (c : ℂ) :
    query encode marked (EuclideanSpace.single (args, π) c) =
      EuclideanSpace.single
        (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2), π) c := by
  classical
  rw [query, Query.linearLift_single, queryBasis_apply]

theorem query_isometry (encode : Encoding N w) (marked : Bool) :
    Isometry (query encode marked) := (query encode marked).isometry

theorem query_norm (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N))) :
    ‖query encode marked ψ‖ = ‖ψ‖ := (query encode marked).norm_map ψ

theorem query_involutive (encode : Encoding N w) (marked : Bool) :
    Function.Involutive (query encode marked) := by
  intro ψ
  ext ⟨args, π⟩
  rw [query_apply, query_apply]
  change ψ (answerArgs encode marked
      (answerArgs encode marked args (permutationAnswer args.2.1.1 π args.2.1.2))
      (permutationAnswer args.2.1.1 π args.2.1.2), π) = ψ (args, π)
  exact congrArg (fun a => ψ (a, π))
    (answerArgs_involutive encode marked (permutationAnswer args.2.1.1 π args.2.1.2) args)

/-- A slice with fixed enable, direction and point retains the marked-answer
register and the exact permutation register. -/
def markedSlice
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (enable inverse : Bool) (x : Fin N) :
    EuclideanSpace ℂ ((Bool × Bits w) × Equiv.Perm (Fin N)) :=
  WithLp.toLp 2 (fun zπ => ψ ((enable, ((inverse, x), zπ.1)), zπ.2))

/-- On its enabled slice, the coherent marked query is exactly the existing
exact marked permutation-query operator. -/
theorem markedSlice_query_enabled (encode : Encoding N w)
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (inverse : Bool) (x : Fin N) :
    markedSlice (query encode true ψ) true inverse x =
      Query.exactMarked encode inverse x (markedSlice ψ true inverse x) := by
  ext ⟨z, π⟩
  rfl

/-- A fixed marker slice of the ordinary query. -/
def ordinarySlice
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (enable inverse : Bool) (x : Fin N) (marker : Bool) :
    EuclideanSpace ℂ (Bits w × Equiv.Perm (Fin N)) :=
  WithLp.toLp 2 (fun zπ => ψ ((enable, ((inverse, x), (marker, zπ.1))), zπ.2))

/-- The ordinary query leaves the marker untouched, and each enabled marker
slice is exactly the existing ordinary permutation-query operator. -/
theorem ordinarySlice_query_enabled (encode : Encoding N w)
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (inverse : Bool) (x : Fin N) (marker : Bool) :
    ordinarySlice (query encode false ψ) true inverse x marker =
      Query.exactOrdinary encode inverse x (ordinarySlice ψ true inverse x marker) := by
  ext ⟨z, π⟩
  change ψ ((true, ((inverse, x), (Bool.xor marker false,
      xor z (encode (permutationAnswer inverse π x))))), π) = _
  rw [Bool.xor_false]
  rfl

/-- Disabled coherent queries act as identity on every marked-answer slice. -/
theorem markedSlice_query_disabled (encode : Encoding N w) (marked : Bool)
    (ψ : EuclideanSpace ℂ (Args N w × Equiv.Perm (Fin N)))
    (inverse : Bool) (x : Fin N) :
    markedSlice (query encode marked ψ) false inverse x =
      markedSlice ψ false inverse x := by
  ext ⟨z, π⟩
  rfl

end QuantumOracle.ExactCoherentQuery
