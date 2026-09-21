import QuantumOracle.Model.Query

/-!
# Database degree from preservation of actual compression blocks

Support means that every amplitude above a database-size level vanishes.
Preservation of the actual deletion fibers implies growth by at most one.
These elementary support arguments do not assume any spectral normalization
or comparison estimate. An operator must separately be shown to preserve
the fibers before the growth theorem applies to it.
-/

noncomputable section

namespace QuantumOracle.BlockSupport

variable {N : ℕ} {Y : Type*} [Fintype Y]

abbrev State (Y : Type*) [Fintype Y] (N : ℕ) :=
  EuclideanSpace ℂ (Y × Database N)

/-- Every amplitude on the deletion fiber above `J` vanishes. -/
def ZeroOnBlock (x : Fin N) (J : Database N) (ψ : State Y N) : Prop :=
  ∀ y I, I.erase x = J → ψ (y, I) = 0

/-- An operator cannot populate an entirely empty deletion fiber. -/
def PreservesBlocks (x : Fin N) (U : State Y N → State Y N) : Prop :=
  ∀ J ψ, ZeroOnBlock x J ψ → ZeroOnBlock x J (U ψ)

/-- The state has no amplitudes on databases of size greater than `t`. -/
def Supported (t : ℕ) (ψ : State Y N) : Prop :=
  ∀ y I, t < I.size → ψ (y, I) = 0

theorem preservesBlocks_id (x : Fin N) :
    PreservesBlocks (Y := Y) x id := by
  intro J ψ h
  exact h

theorem preservesBlocks_comp {x : Fin N} {U V : State Y N → State Y N}
    (hU : PreservesBlocks x U) (hV : PreservesBlocks x V) :
    PreservesBlocks x (U ∘ V) := by
  intro J ψ h
  exact hU J (V ψ) (hV J ψ h)

theorem supported_mono {s t : ℕ} {ψ : State Y N}
    (hst : s ≤ t) (hψ : Supported s ψ) : Supported t ψ := by
  intro y I hI
  exact hψ y I (hst.trans_lt hI)

/-- Deleting one input removes at most one database edge. -/
theorem size_le_erase_add_one (x : Fin N) (I : Database N) :
    I.size ≤ (I.erase x).size + 1 := by
  by_cases hx : x ∈ I.domain
  · have h := Finset.card_erase_add_one hx
    simpa only [Database.size, Database.erase_domain] using h.ge
  · rw [Database.erase_eq_self_of_undefined I x hx]
    exact Nat.le_succ _

/-- Any two databases in one actual compression block differ in size by at most one. -/
theorem size_le_of_same_erase (x : Fin N) (I K : Database N)
    (h : I.erase x = K.erase x) : I.size ≤ K.size + 1 := by
  calc
    I.size ≤ (I.erase x).size + 1 := size_le_erase_add_one x I
    _ = (K.erase x).size + 1 := by rw [h]
    _ ≤ K.size + 1 := Nat.add_le_add_right (Database.erase_size_le K x) 1

/-- A block-preserving map increases database degree by at most one. -/
theorem supported_succ_of_preservesBlocks {x : Fin N}
    {U : State Y N → State Y N} {t : ℕ} {ψ : State Y N}
    (hU : PreservesBlocks x U) (hψ : Supported t ψ) :
    Supported (t + 1) (U ψ) := by
  intro y I hI
  apply hU (I.erase x) ψ ?_ y I rfl
  intro z K hK
  apply hψ z K
  have hbound := size_le_of_same_erase x I K hK.symm
  omega

/-- Database inversion acts on amplitudes by the actual involutive graph swap. -/
def inverseState (ψ : State Y N) : State Y N :=
  WithLp.toLp 2 (fun p => ψ (p.1, p.2.inverse))

@[simp] theorem inverseState_apply (ψ : State Y N) (y : Y) (I : Database N) :
    inverseState ψ (y, I) = ψ (y, I.inverse) := rfl

@[simp] theorem inverseState_inverseState (ψ : State Y N) :
    inverseState (inverseState ψ) = ψ := by
  ext ⟨y, I⟩
  change ψ (y, I.inverse.inverse) = ψ (y, I)
  rw [Database.inverse_inverse]

theorem supported_inverseState {t : ℕ} {ψ : State Y N}
    (hψ : Supported t ψ) : Supported t (inverseState ψ) := by
  intro y I hI
  exact hψ y I.inverse (by simpa only [Database.inverse_size] using hI)

theorem inverseState_eq_linearLift_flip (ψ : State Y N) :
    inverseState ψ = Query.linearLift BasisLookup.flip ψ := by
  ext ⟨y, I⟩
  rfl

theorem supported_flip {t : ℕ} {ψ : State Y N}
    (hψ : Supported t ψ) :
    Supported t (Query.linearLift BasisLookup.flip ψ) := by
  rw [← inverseState_eq_linearLift_flip]
  exact supported_inverseState hψ

/-- Arbitrary initial workspace amplitudes tensored with the empty database. -/
def emptyState (ψ : EuclideanSpace ℂ Y) : State Y N :=
  WithLp.toLp 2 (fun p => if p.2 = Database.empty then ψ p.1 else 0)

theorem supported_emptyState (ψ : EuclideanSpace ℂ Y) :
    Supported 0 (emptyState (N := N) ψ) := by
  intro y I hI
  have hne : I ≠ Database.empty := by
    intro h
    subst I
    simp at hI
  simp [emptyState, hne]

theorem supported_single_empty [DecidableEq Y] (y : Y) (a : ℂ) :
    Supported 0 (EuclideanSpace.single (y, (Database.empty : Database N)) a) := by
  intro z I hI
  have hne : (z, I) ≠ (y, (Database.empty : Database N)) := by
    intro h
    have hdb : I = Database.empty := congrArg Prod.snd h
    simp [hdb] at hI
  simp [EuclideanSpace.single_apply, hne]

section Indexed

variable {C : Type*} [Fintype C]

/-- The amplitudes in one coherent-control branch. -/
def slice (ψ : State (C × Y) N) (c : C) : State Y N :=
  WithLp.toLp 2 (fun p => ψ ((c, p.1), p.2))

/-- Apply a family independently on the coherent index register. -/
def indexed (U : C → State Y N → State Y N) (ψ : State (C × Y) N) :
    State (C × Y) N :=
  WithLp.toLp 2 (fun p => U p.1.1 (slice ψ p.1.1) (p.1.2, p.2))

@[simp] theorem indexed_apply (U : C → State Y N → State Y N)
    (ψ : State (C × Y) N) (c : C) (y : Y) (I : Database N) :
    indexed U ψ ((c, y), I) = U c (slice ψ c) (y, I) := rfl

theorem preservesBlocks_indexed {x : Fin N} {U : C → State Y N → State Y N}
    (hU : ∀ c, PreservesBlocks x (U c)) : PreservesBlocks x (indexed U) := by
  intro J ψ hψ cY I hI
  exact hU cY.1 J (slice ψ cY.1) (fun y K hK => hψ (cY.1, y) K hK)
    cY.2 I hI

theorem supported_slice {t : ℕ} {ψ : State (C × Y) N}
    (hψ : Supported t ψ) (c : C) : Supported t (slice ψ c) := by
  intro y I hI
  exact hψ (c, y) I hI

/-- Each coherent branch may use a different input/direction, provided it has
the same proved support bound. -/
theorem supported_indexed {t s : ℕ} {U : C → State Y N → State Y N}
    (hU : ∀ c ψ, Supported t ψ → Supported s (U c ψ))
    {ψ : State (C × Y) N} (hψ : Supported t ψ) : Supported s (indexed U ψ) := by
  intro cY I hI
  exact hU cY.1 (slice ψ cY.1) (supported_slice hψ cY.1) cY.2 I hI

end Indexed

/-- A finite sequence of state transitions. -/
def run (U : ℕ → State Y N → State Y N) (ψ : State Y N) : ℕ → State Y N
  | 0 => ψ
  | q + 1 => U q (run U ψ q)

/-- Degree grows by at most the number of transitions whose one-step support
growth has been proved. Workspace operations may be incorporated in each step. -/
theorem supported_run {U : ℕ → State Y N → State Y N} {ψ : State Y N} {t : ℕ}
    (hU : ∀ q s φ, Supported s φ → Supported (s + 1) (U q φ))
    (hψ : Supported t ψ) (q : ℕ) : Supported (t + q) (run U ψ q) := by
  induction q with
  | zero => simpa only [Nat.add_zero, run] using hψ
  | succ q ih =>
    simpa only [run, Nat.add_assoc] using hU q (t + q) (run U ψ q) ih

end QuantumOracle.BlockSupport
