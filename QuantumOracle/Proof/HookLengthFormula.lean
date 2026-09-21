/-
SPDX-FileCopyrightText: 2026 Advameg, Inc.
SPDX-License-Identifier: Apache-2.0

Adapted for this project using Lean/mathlib 4.32.2.
The byte-for-byte upstream source, license, notice and checker evidence are in
vendor/proofatlas/hook-length-formula/. See that directory's README.md.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import QuantumOracle.Proof.HookLengthCompat

/-!
# Hook-Length Formula Seed

This file prepares a proof-facing statement over mathlib `YoungDiagram`. The
minimum endpoint defines standard tableaux as order-preserving bijections from
cells to `Fin μ.card` and uses a multiplicative form to avoid natural-number
division in the theorem statement.
-/

open scoped BigOperators
open Polynomial

namespace AtlasKnownTheorems.HookLengthFormula

attribute [local instance] Classical.propDecidable

/-- Cells of a Young diagram as a finite subtype. -/
abbrev Cell (μ : YoungDiagram) := {c : ℕ × ℕ // c ∈ μ.cells}

/-- The local cell subtype has cardinality equal to the diagram cardinality. -/
theorem cell_fintype_card (μ : YoungDiagram) :
    Fintype.card (Cell μ) = μ.card := by
  change Fintype.card {p // p ∈ μ.cells} = μ.cells.card
  exact Fintype.card_coe μ.cells

/-- A Young diagram's cardinality is the sum of its row lengths. -/
theorem card_eq_sum_rowLen (μ : YoungDiagram) :
    μ.card = (Finset.range (μ.colLen 0)).sum μ.rowLen := by
  have hmaps : ∀ c ∈ μ.cells, c.fst ∈ Finset.range (μ.colLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have hcell : c ∈ μ := by
      rwa [← YoungDiagram.mem_cells]
    have hzero : (c.fst, 0) ∈ μ := by
      exact μ.isLowerSet (by exact ⟨le_rfl, Nat.zero_le c.snd⟩) hcell
    exact YoungDiagram.mem_iff_lt_colLen.mp hzero
  rw [YoungDiagram.card]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [YoungDiagram.rowLen_eq_card]
  rfl

/-- Embed local cells back into coordinate pairs. -/
def cellValEmbedding (μ : YoungDiagram) : Cell μ ↪ ℕ × ℕ where
  toFun c := c.val
  inj' := by
    intro a b h
    apply Subtype.ext
    exact h

/-- Product-order comparability of cells, used for the minimum standard-tableau predicate. -/
def CellLe {μ : YoungDiagram} (a b : Cell μ) : Prop :=
  a.val.1 ≤ b.val.1 ∧ a.val.2 ≤ b.val.2

/-- A removable corner cell: no distinct cell lies weakly below-and-right of it. -/
def IsCornerCell (μ : YoungDiagram) (c : Cell μ) : Prop :=
  ∀ d : Cell μ, CellLe c d → d = c

/-- Corner cells of a Young diagram. -/
abbrev CornerCells (μ : YoungDiagram) : Type :=
  {c : Cell μ // IsCornerCell μ c}

/-- Every nonempty Young diagram has a corner cell. -/
theorem exists_isCornerCell_of_nonempty (μ : YoungDiagram) (hμ : μ.cells.Nonempty) :
    ∃ c : Cell μ, IsCornerCell μ c := by
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image μ.cells (fun p : ℕ × ℕ ↦ p.1 + p.2) hμ
  refine ⟨⟨x, hx⟩, ?_⟩
  intro d hd
  change x.1 ≤ d.val.1 ∧ x.2 ≤ d.val.2 at hd
  have hmaxd := hmax d.val d.property
  apply Subtype.ext
  change d.val = x
  apply Prod.ext <;> omega

/-- Remove a corner cell from a Young diagram. -/
def eraseCorner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) : YoungDiagram where
  cells := μ.cells.erase c.val
  isLowerSet := by
    intro upper lower hle hupper
    rw [Finset.mem_coe, Finset.mem_erase] at hupper ⊢
    rcases hupper with ⟨hupper_ne, hupper_mem⟩
    refine ⟨?_, μ.isLowerSet hle hupper_mem⟩
    intro hlower
    apply hupper_ne
    have hcorner : (⟨upper, hupper_mem⟩ : Cell μ) = c := by
      apply hc
      change c.val.1 ≤ upper.1 ∧ c.val.2 ≤ upper.2
      simpa only [hlower] using (Prod.mk_le_mk.mp hle)
    simpa using congrArg Subtype.val hcorner

@[simp]
theorem eraseCorner_cells (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (eraseCorner μ c hc).cells = μ.cells.erase c.val :=
  rfl

@[simp]
theorem mem_eraseCorner_cells_iff (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c)
    (p : ℕ × ℕ) :
    p ∈ (eraseCorner μ c hc).cells ↔ p ∈ μ.cells ∧ p ≠ c.val := by
  simp [eraseCorner, and_comm]

theorem eraseCorner_card_add_one (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (eraseCorner μ c hc).card + 1 = μ.card := by
  change (μ.cells.erase c.val).card + 1 = μ.cells.card
  exact Finset.card_erase_add_one c.property

theorem eraseCorner_card_lt (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (eraseCorner μ c hc).card < μ.card := by
  have h := eraseCorner_card_add_one μ c hc
  omega

/-- The canonical inclusion of cells after erasing a corner back into the original diagram. -/
def eraseCornerCellEmbedding (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    Cell (eraseCorner μ c hc) ↪ Cell μ where
  toFun d := ⟨d.val, ((mem_eraseCorner_cells_iff μ c hc d.val).mp d.property).1⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : Cell μ ↦ x.val) h

@[simp]
theorem eraseCornerCellEmbedding_apply_val (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc)) :
    (eraseCornerCellEmbedding μ c hc d).val = d.val :=
  rfl

theorem eraseCornerCellEmbedding_ne_corner (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc)) :
    eraseCornerCellEmbedding μ c hc d ≠ c := by
  intro hdc
  exact ((mem_eraseCorner_cells_iff μ c hc d.val).mp d.property).2
    (by simpa using congrArg Subtype.val hdc)

/-- Reinterpret a non-erased cell of `μ` as a cell of `eraseCorner μ c hc`. -/
def eraseCornerCellOfNe (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell μ) (hd : d ≠ c) :
    Cell (eraseCorner μ c hc) :=
  ⟨d.val, by
    rw [mem_eraseCorner_cells_iff]
    refine ⟨d.property, ?_⟩
    intro hval
    apply hd
    apply Subtype.ext
    exact hval⟩

@[simp]
theorem eraseCornerCellEmbedding_eraseCornerCellOfNe (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell μ) (hd : d ≠ c) :
    eraseCornerCellEmbedding μ c hc (eraseCornerCellOfNe μ c hc d hd) = d := by
  apply Subtype.ext
  rfl

@[simp]
theorem eraseCornerCellOfNe_eraseCornerCellEmbedding (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc))
    (hd : eraseCornerCellEmbedding μ c hc d ≠ c) :
    eraseCornerCellOfNe μ c hc (eraseCornerCellEmbedding μ c hc d) hd = d := by
  apply Subtype.ext
  rfl

/-- Cells of the erased diagram are equivalent to original cells other than the erased corner. -/
noncomputable def eraseCornerCellEquivNe (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    Cell (eraseCorner μ c hc) ≃ {d : Cell μ // d ≠ c} where
  toFun d := ⟨eraseCornerCellEmbedding μ c hc d, eraseCornerCellEmbedding_ne_corner μ c hc d⟩
  invFun d := eraseCornerCellOfNe μ c hc d.1 d.2
  left_inv d := by
    apply eraseCornerCellOfNe_eraseCornerCellEmbedding
  right_inv d := by
    apply Subtype.ext
    exact eraseCornerCellEmbedding_eraseCornerCellOfNe μ c hc d.1 d.2

/-- Mapping erased-shape cells back into `μ` gives exactly the original non-corner cells. -/
theorem eraseCornerCellEmbedding_attach_map (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    (eraseCorner μ c hc).cells.attach.map (eraseCornerCellEmbedding μ c hc) =
      μ.cells.attach.erase c := by
  ext d
  constructor
  · intro hd
    rw [Finset.mem_map] at hd
    rcases hd with ⟨e, _he, hed⟩
    rw [← hed]
    simp [eraseCornerCellEmbedding_ne_corner]
  · intro hd
    rw [Finset.mem_erase] at hd
    exact Finset.mem_map.mpr
      ⟨eraseCornerCellOfNe μ c hc d hd.1, Finset.mem_attach _ _, by simp⟩

/-- Delete a pivot from `Fin (n + 1)` by choosing its `succAbove` preimage. -/
noncomputable def finDelete {n : ℕ} (p y : Fin (n + 1)) (h : y ≠ p) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq h)

/-- The value selected by `finDelete` relabels back to the original non-pivot value. -/
theorem succAbove_finDelete {n : ℕ} (p y : Fin (n + 1)) (h : y ≠ p) :
    p.succAbove (finDelete p y h) = y :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

/--
Relabel the value of a cell in an erased-corner shape by deleting the original
corner value from `Fin μ.card`.
-/
noncomputable def eraseCornerRelabelValue (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) (d : Cell (eraseCorner μ c hc)) :
    Fin (eraseCorner μ c hc).card :=
  let hcard := eraseCorner_card_add_one μ c hc
  let pivot : Fin ((eraseCorner μ c hc).card + 1) := Fin.cast hcard.symm (T c)
  let value : Fin ((eraseCorner μ c hc).card + 1) :=
    Fin.cast hcard.symm (T (eraseCornerCellEmbedding μ c hc d))
  finDelete pivot value (by
    intro h
    have hvalue : T (eraseCornerCellEmbedding μ c hc d) = T c :=
      Fin.cast_injective hcard.symm h
    exact eraseCornerCellEmbedding_ne_corner μ c hc d (hTinj hvalue))

/--
The relabelled erased-corner value is exactly the `succAbove` preimage of the
old tableau value after casting along the erased-cardinality identity.
-/
theorem succAbove_eraseCornerRelabelValue (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) (d : Cell (eraseCorner μ c hc)) :
    (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
      (eraseCornerRelabelValue μ c hc hTinj d) =
    Fin.cast (eraseCorner_card_add_one μ c hc).symm
      (T (eraseCornerCellEmbedding μ c hc d)) := by
  unfold eraseCornerRelabelValue
  exact succAbove_finDelete _ _ _

/-- Restrict a tableau to an erased-corner shape and relabel its values. -/
noncomputable def eraseCornerRestrictTableau (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) :
    Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card :=
  fun d ↦ eraseCornerRelabelValue μ c hc hTinj d

/-- The erased-corner restriction is injective when the original filling is injective. -/
theorem eraseCornerRestrictTableau_injective (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) :
    Function.Injective (eraseCornerRestrictTableau μ c hc hTinj) := by
  intro d e hde
  unfold eraseCornerRestrictTableau at hde
  have hsucc :=
    congrArg
      (fun x ↦ (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove x)
      hde
  change (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
      (eraseCornerRelabelValue μ c hc hTinj d) =
    (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
      (eraseCornerRelabelValue μ c hc hTinj e) at hsucc
  rw [succAbove_eraseCornerRelabelValue, succAbove_eraseCornerRelabelValue] at hsucc
  have hvalue : T (eraseCornerCellEmbedding μ c hc d) =
      T (eraseCornerCellEmbedding μ c hc e) :=
    Fin.cast_injective (eraseCorner_card_add_one μ c hc).symm hsucc
  have hemb : eraseCornerCellEmbedding μ c hc d = eraseCornerCellEmbedding μ c hc e :=
    hTinj hvalue
  exact (eraseCornerCellEmbedding μ c hc).injective hemb

/-- The erased-corner restriction is bijective when the original filling is injective. -/
theorem eraseCornerRestrictTableau_bijective (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) :
    Function.Bijective (eraseCornerRestrictTableau μ c hc hTinj) := by
  refine ⟨eraseCornerRestrictTableau_injective μ c hc hTinj, ?_⟩
  have hcard :
      Fintype.card (Cell (eraseCorner μ c hc)) =
        Fintype.card (Fin (eraseCorner μ c hc).card) := by
    rw [cell_fintype_card, Fintype.card_fin]
  exact (eraseCornerRestrictTableau_injective μ c hc hTinj).surjective_of_finite
    (Fintype.equivOfCardEq hcard)

/-- Cells in the hook of `c`: same row to the right or same column below. -/
def hookCells (μ : YoungDiagram) (c : Cell μ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun d ↦
    (d.1 = c.val.1 ∧ c.val.2 ≤ d.2) ∨
      (d.2 = c.val.2 ∧ c.val.1 ≤ d.1)

/-- A cell is always contained in its own hook. -/
@[simp]
theorem mem_hookCells_self (μ : YoungDiagram) (c : Cell μ) : c.val ∈ hookCells μ c := by
  simp [hookCells, c.property]

/-- Coordinate characterization for one cell lying in another cell's hook. -/
theorem corner_mem_hookCells_iff (μ : YoungDiagram) (c d : Cell μ) :
    c.val ∈ hookCells μ d ↔
      (c.val.1 = d.val.1 ∧ d.val.2 ≤ c.val.2) ∨
        (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1) := by
  simp [hookCells, c.property]

/-- Strict coordinate characterization for a non-self cell lying in another cell's hook. -/
theorem corner_mem_hookCells_iff_of_ne (μ : YoungDiagram) (c d : Cell μ)
    (hd : d ≠ c) :
    c.val ∈ hookCells μ d ↔
      (c.val.1 = d.val.1 ∧ d.val.2 < c.val.2) ∨
        (c.val.2 = d.val.2 ∧ d.val.1 < c.val.1) := by
  rw [corner_mem_hookCells_iff]
  constructor
  · intro h
    rcases h with hrow | hcol
    · left
      refine ⟨hrow.1, ?_⟩
      have hne : d.val.2 ≠ c.val.2 := by
        intro h2
        apply hd
        apply Subtype.ext
        exact Prod.ext hrow.1.symm h2
      exact lt_of_le_of_ne hrow.2 hne
    · right
      refine ⟨hcol.1, ?_⟩
      have hne : d.val.1 ≠ c.val.1 := by
        intro h1
        apply hd
        apply Subtype.ext
        exact Prod.ext h1 hcol.1.symm
      exact lt_of_le_of_ne hcol.2 hne
  · intro h
    rcases h with hrow | hcol
    · left
      exact ⟨hrow.1, le_of_lt hrow.2⟩
    · right
      exact ⟨hcol.1, le_of_lt hcol.2⟩

/-- Cells in the erased corner's row whose hook is affected by erasing the corner. -/
def hookAffectedRowCells (μ : YoungDiagram) (c : Cell μ) : Finset (Cell μ) :=
  μ.cells.attach.filter fun d => c.val.1 = d.val.1 ∧ d.val.2 < c.val.2

/-- Cells in the erased corner's column whose hook is affected by erasing the corner. -/
def hookAffectedColCells (μ : YoungDiagram) (c : Cell μ) : Finset (Cell μ) :=
  μ.cells.attach.filter fun d => c.val.2 = d.val.2 ∧ d.val.1 < c.val.1

/-- Non-corner cells whose hook is affected by erasing the corner. -/
def hookAffectedCells (μ : YoungDiagram) (c : Cell μ) : Finset (Cell μ) :=
  (μ.cells.attach.erase c).filter fun d => c.val ∈ hookCells μ d

/-- Affected hook cells are exactly the row-affected cells union the column-affected cells. -/
theorem hookAffectedCells_eq_row_union_col (μ : YoungDiagram) (c : Cell μ) :
    hookAffectedCells μ c = hookAffectedRowCells μ c ∪ hookAffectedColCells μ c := by
  ext d
  by_cases hd : d = c
  · subst d
    simp [hookAffectedCells, hookAffectedRowCells, hookAffectedColCells]
  · simp [hookAffectedCells, hookAffectedRowCells, hookAffectedColCells,
      corner_mem_hookCells_iff_of_ne μ c d hd]
    exact fun _ => hd

/-- Row-affected and column-affected cells are disjoint. -/
theorem hookAffectedRowCells_disjoint_hookAffectedColCells (μ : YoungDiagram)
    (c : Cell μ) :
    Disjoint (hookAffectedRowCells μ c) (hookAffectedColCells μ c) := by
  rw [Finset.disjoint_left]
  intro d hdrow hdcol
  simp [hookAffectedRowCells] at hdrow
  simp [hookAffectedColCells] at hdcol
  omega

/-- Products over affected cells split into row-affected and column-affected parts. -/
theorem hookAffectedCells_prod_eq_row_mul_col (μ : YoungDiagram) (c : Cell μ)
    (f : Cell μ → ℕ) :
    (hookAffectedCells μ c).prod f =
      (hookAffectedRowCells μ c).prod f * (hookAffectedColCells μ c).prod f := by
  rw [hookAffectedCells_eq_row_union_col]
  exact Finset.prod_union (hookAffectedRowCells_disjoint_hookAffectedColCells μ c)

/--
The cell in the erased corner's row at column `j`, returning the corner itself
outside the useful interval.
-/
def hookAffectedRowCellOfIndex (μ : YoungDiagram) (c : Cell μ) (j : ℕ) : Cell μ :=
  if h : j ≤ c.val.2 then
    ⟨(c.val.1, j), μ.up_left_mem le_rfl h c.property⟩
  else c

/-- On columns strictly before the corner, `hookAffectedRowCellOfIndex` is the expected cell. -/
theorem hookAffectedRowCellOfIndex_of_lt (μ : YoungDiagram) (c : Cell μ)
    {j : ℕ} (hj : j < c.val.2) :
    hookAffectedRowCellOfIndex μ c j =
      ⟨(c.val.1, j), μ.up_left_mem le_rfl (le_of_lt hj) c.property⟩ := by
  unfold hookAffectedRowCellOfIndex
  rw [dif_pos (le_of_lt hj)]

/-- An interval-indexed row cell is row-affected. -/
theorem hookAffectedRowCellOfIndex_mem (μ : YoungDiagram) (c : Cell μ)
    {j : ℕ} (hj : j ∈ Finset.Ico 0 c.val.2) :
    hookAffectedRowCellOfIndex μ c j ∈ hookAffectedRowCells μ c := by
  rw [Finset.mem_Ico] at hj
  rw [hookAffectedRowCellOfIndex_of_lt μ c hj.2]
  simp [hookAffectedRowCells, hj.2]

/-- Row-affected cells reindex as the coordinate interval left of the erased corner. -/
theorem hookAffectedRowCells_map_cellValEmbedding (μ : YoungDiagram) (c : Cell μ) :
    (hookAffectedRowCells μ c).map (cellValEmbedding μ) =
      {c.val.1} ×ˢ Finset.Ico 0 c.val.2 := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    rcases hp with ⟨d, hd, hdp⟩
    simp [hookAffectedRowCells] at hd
    rw [← hdp]
    rw [Finset.mem_product]
    constructor
    · simpa [cellValEmbedding] using hd.1.symm
    · rw [Finset.mem_Ico]
      exact ⟨Nat.zero_le _, hd.2⟩
  · intro hp
    rw [Finset.mem_product] at hp
    rcases hp with ⟨hrow, hcol⟩
    rw [Finset.mem_singleton] at hrow
    rw [Finset.mem_Ico] at hcol
    refine Finset.mem_map.mpr ?_
    let d : Cell μ := ⟨p, by
      have hle : p.2 ≤ c.val.2 := le_of_lt hcol.2
      rw [show p = (c.val.1, p.2) by exact Prod.ext hrow rfl]
      exact μ.up_left_mem le_rfl hle c.property⟩
    refine ⟨d, ?_, ?_⟩
    · simp [hookAffectedRowCells, d, hrow, hcol.2]
    · rfl

/-- The row-affected cells in a corner's row are exactly the earlier columns. -/
theorem hookAffectedRowCells_card (μ : YoungDiagram) (c : Cell μ) :
    (hookAffectedRowCells μ c).card = c.val.2 := by
  rw [← Finset.card_map (f := cellValEmbedding μ)]
  rw [hookAffectedRowCells_map_cellValEmbedding, Finset.card_product, Nat.card_Ico]
  simp

/-- Reindex a product over row-affected cells by the interval of earlier columns. -/
theorem hookAffectedRowCells_prod_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (f : Cell μ → ℕ) :
    (hookAffectedRowCells μ c).prod f =
      (Finset.Ico 0 c.val.2).prod (fun j => f (hookAffectedRowCellOfIndex μ c j)) := by
  apply Finset.prod_bij (fun d _hd => d.val.2)
  · intro d hd
    simp [hookAffectedRowCells] at hd
    rw [Finset.mem_Ico]
    exact ⟨Nat.zero_le _, hd.2⟩
  · intro d1 hd1 d2 hd2 hcol
    simp [hookAffectedRowCells] at hd1 hd2
    apply Subtype.ext
    exact Prod.ext (by omega) hcol
  · intro j hj
    refine ⟨hookAffectedRowCellOfIndex μ c j, ?_, ?_⟩
    · exact hookAffectedRowCellOfIndex_mem μ c hj
    · rw [Finset.mem_Ico] at hj
      rw [hookAffectedRowCellOfIndex_of_lt μ c hj.2]
  · intro d hd
    simp [hookAffectedRowCells] at hd
    congr 1
    rw [hookAffectedRowCellOfIndex_of_lt μ c hd.2]
    apply Subtype.ext
    exact Prod.ext hd.1.symm rfl

/--
The cell in the erased corner's column at row `i`, returning the corner itself
outside the useful interval.
-/
def hookAffectedColCellOfIndex (μ : YoungDiagram) (c : Cell μ) (i : ℕ) : Cell μ :=
  if h : i ≤ c.val.1 then
    ⟨(i, c.val.2), μ.up_left_mem h le_rfl c.property⟩
  else c

/-- On rows strictly above the corner, `hookAffectedColCellOfIndex` is the expected cell. -/
theorem hookAffectedColCellOfIndex_of_lt (μ : YoungDiagram) (c : Cell μ)
    {i : ℕ} (hi : i < c.val.1) :
    hookAffectedColCellOfIndex μ c i =
      ⟨(i, c.val.2), μ.up_left_mem (le_of_lt hi) le_rfl c.property⟩ := by
  unfold hookAffectedColCellOfIndex
  rw [dif_pos (le_of_lt hi)]

/-- An interval-indexed column cell is column-affected. -/
theorem hookAffectedColCellOfIndex_mem (μ : YoungDiagram) (c : Cell μ)
    {i : ℕ} (hi : i ∈ Finset.Ico 0 c.val.1) :
    hookAffectedColCellOfIndex μ c i ∈ hookAffectedColCells μ c := by
  rw [Finset.mem_Ico] at hi
  rw [hookAffectedColCellOfIndex_of_lt μ c hi.2]
  simp [hookAffectedColCells, hi.2]

/-- Column-affected cells reindex as the coordinate interval above the erased corner. -/
theorem hookAffectedColCells_map_cellValEmbedding (μ : YoungDiagram) (c : Cell μ) :
    (hookAffectedColCells μ c).map (cellValEmbedding μ) =
      Finset.Ico 0 c.val.1 ×ˢ {c.val.2} := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    rcases hp with ⟨d, hd, hdp⟩
    simp [hookAffectedColCells] at hd
    rw [← hdp]
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_Ico]
      exact ⟨Nat.zero_le _, hd.2⟩
    · simpa [cellValEmbedding] using hd.1.symm
  · intro hp
    rw [Finset.mem_product] at hp
    rcases hp with ⟨hrow, hcol⟩
    rw [Finset.mem_Ico] at hrow
    rw [Finset.mem_singleton] at hcol
    refine Finset.mem_map.mpr ?_
    let d : Cell μ := ⟨p, by
      have hle : p.1 ≤ c.val.1 := le_of_lt hrow.2
      rw [show p = (p.1, c.val.2) by exact Prod.ext rfl hcol]
      exact μ.up_left_mem hle le_rfl c.property⟩
    refine ⟨d, ?_, ?_⟩
    · simp [hookAffectedColCells, d, hcol, hrow.2]
    · rfl

/-- The column-affected cells in a corner's column are exactly the earlier rows. -/
theorem hookAffectedColCells_card (μ : YoungDiagram) (c : Cell μ) :
    (hookAffectedColCells μ c).card = c.val.1 := by
  rw [← Finset.card_map (f := cellValEmbedding μ)]
  rw [hookAffectedColCells_map_cellValEmbedding, Finset.card_product, Nat.card_Ico]
  simp

/-- Reindex a product over column-affected cells by the interval of earlier rows. -/
theorem hookAffectedColCells_prod_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (f : Cell μ → ℕ) :
    (hookAffectedColCells μ c).prod f =
      (Finset.Ico 0 c.val.1).prod (fun i => f (hookAffectedColCellOfIndex μ c i)) := by
  apply Finset.prod_bij (fun d _hd => d.val.1)
  · intro d hd
    simp [hookAffectedColCells] at hd
    rw [Finset.mem_Ico]
    exact ⟨Nat.zero_le _, hd.2⟩
  · intro d1 hd1 d2 hd2 hrow
    simp [hookAffectedColCells] at hd1 hd2
    apply Subtype.ext
    exact Prod.ext hrow (by omega)
  · intro i hi
    refine ⟨hookAffectedColCellOfIndex μ c i, ?_, ?_⟩
    · exact hookAffectedColCellOfIndex_mem μ c hi
    · rw [Finset.mem_Ico] at hi
      rw [hookAffectedColCellOfIndex_of_lt μ c hi.2]
  · intro d hd
    simp [hookAffectedColCells] at hd
    congr 1
    rw [hookAffectedColCellOfIndex_of_lt μ c hd.2]
    apply Subtype.ext
    exact Prod.ext rfl hd.1.symm

/-- The row slice of a hook, as coordinate cells weakly right of the base cell. -/
def hookRowCells (μ : YoungDiagram) (c : Cell μ) : Finset (ℕ × ℕ) :=
  (μ.row c.val.1).filter fun p => c.val.2 ≤ p.2

/-- The column slice of a hook, as coordinate cells weakly below the base cell. -/
def hookColCells (μ : YoungDiagram) (c : Cell μ) : Finset (ℕ × ℕ) :=
  (μ.col c.val.2).filter fun p => c.val.1 ≤ p.1

/-- The base cell belongs to the row slice of its hook. -/
@[simp]
theorem mem_hookRowCells_self (μ : YoungDiagram) (c : Cell μ) :
    c.val ∈ hookRowCells μ c := by
  simp [hookRowCells, YoungDiagram.mem_row_iff]

/-- The base cell belongs to the column slice of its hook. -/
@[simp]
theorem mem_hookColCells_self (μ : YoungDiagram) (c : Cell μ) :
    c.val ∈ hookColCells μ c := by
  simp [hookColCells, YoungDiagram.mem_col_iff]

/-- A hook is the union of its row and column slices. -/
theorem hookCells_eq_hookRowCells_union_hookColCells (μ : YoungDiagram) (c : Cell μ) :
    hookCells μ c = hookRowCells μ c ∪ hookColCells μ c := by
  ext p
  simp [hookCells, hookRowCells, hookColCells, YoungDiagram.mem_row_iff,
    YoungDiagram.mem_col_iff, and_left_comm, and_assoc, and_or_left]

/-- The row and column slices of a hook meet only at the base cell. -/
theorem hookRowCells_inter_hookColCells (μ : YoungDiagram) (c : Cell μ) :
    hookRowCells μ c ∩ hookColCells μ c = {c.val} := by
  ext p
  simp [hookRowCells, hookColCells, YoungDiagram.mem_row_iff, YoungDiagram.mem_col_iff]
  constructor
  · intro h
    exact Prod.ext h.1.1.2 h.2.1.2
  · intro h
    subst p
    exact ⟨⟨⟨c.property, rfl⟩, le_rfl⟩, ⟨⟨c.property, rfl⟩, le_rfl⟩⟩

/-- Hook length of a cell, interpreted relative to the finite Young diagram. -/
def hookLength (μ : YoungDiagram) (c : Cell μ) : ℕ :=
  (hookCells μ c).card

/-- Hook length as the row-slice size plus column-slice size, with the base cell counted once. -/
theorem hookLength_eq_row_card_add_col_card_sub_one (μ : YoungDiagram) (c : Cell μ) :
    hookLength μ c = (hookRowCells μ c).card + (hookColCells μ c).card - 1 := by
  rw [hookLength, hookCells_eq_hookRowCells_union_hookColCells]
  rw [Finset.card_union, hookRowCells_inter_hookColCells]
  simp

/-- The row slice of a hook is a singleton row coordinate times an interval of columns. -/
theorem hookRowCells_eq_singleton_prod_Ico (μ : YoungDiagram) (c : Cell μ) :
    hookRowCells μ c = {c.val.1} ×ˢ Finset.Ico c.val.2 (μ.rowLen c.val.1) := by
  ext p
  simp only [hookRowCells, YoungDiagram.row_eq_prod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_range, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨h.1.1, ⟨h.2, h.1.2⟩⟩
  · intro h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩

/-- Cardinality of the row slice of a hook in terms of the row length. -/
theorem hookRowCells_card (μ : YoungDiagram) (c : Cell μ) :
    (hookRowCells μ c).card = μ.rowLen c.val.1 - c.val.2 := by
  rw [hookRowCells_eq_singleton_prod_Ico]
  rw [Finset.card_product, Nat.card_Ico]
  simp

/-- The column slice of a hook is an interval of rows times a singleton column coordinate. -/
theorem hookColCells_eq_Ico_prod_singleton (μ : YoungDiagram) (c : Cell μ) :
    hookColCells μ c = Finset.Ico c.val.1 (μ.colLen c.val.2) ×ˢ {c.val.2} := by
  ext p
  simp only [hookColCells, YoungDiagram.col_eq_prod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_range, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨⟨h.2, h.1.1⟩, h.1.2⟩
  · intro h
    exact ⟨⟨h.1.2, h.2⟩, h.1.1⟩

/-- Cardinality of the column slice of a hook in terms of the column length. -/
theorem hookColCells_card (μ : YoungDiagram) (c : Cell μ) :
    (hookColCells μ c).card = μ.colLen c.val.2 - c.val.1 := by
  rw [hookColCells_eq_Ico_prod_singleton]
  rw [Finset.card_product, Nat.card_Ico]
  simp

/-- Hook length in terms of the ambient row and column lengths. -/
theorem hookLength_eq_rowLen_sub_add_colLen_sub_sub_one (μ : YoungDiagram) (c : Cell μ) :
    hookLength μ c =
      (μ.rowLen c.val.1 - c.val.2) + (μ.colLen c.val.2 - c.val.1) - 1 := by
  rw [hookLength_eq_row_card_add_col_card_sub_one, hookRowCells_card, hookColCells_card]

/-- A corner's row stops exactly at that corner. -/
theorem rowLen_corner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    μ.rowLen c.val.1 = c.val.2 + 1 := by
  have hlt : c.val.2 < μ.rowLen c.val.1 := by
    simpa using
      (YoungDiagram.mem_iff_lt_rowLen (μ := μ) (i := c.val.1) (j := c.val.2)).mp
        c.property
  apply le_antisymm
  · by_contra hle
    have hgt : c.val.2 + 1 < μ.rowLen c.val.1 := Nat.lt_of_not_ge hle
    let d : Cell μ := ⟨(c.val.1, c.val.2 + 1), by
      exact
        (YoungDiagram.mem_iff_lt_rowLen (μ := μ) (i := c.val.1) (j := c.val.2 + 1)).mpr
          hgt⟩
    have hle_cd : CellLe c d := by
      change c.val.1 ≤ d.val.1 ∧ c.val.2 ≤ d.val.2
      simp [d]
    have hdc : d = c := hc d hle_cd
    have hval := congrArg Subtype.val hdc
    have hcol := congrArg Prod.snd hval
    change c.val.2 + 1 = c.val.2 at hcol
    omega
  · exact Nat.succ_le_of_lt hlt

/-- A corner's column stops exactly at that corner. -/
theorem colLen_corner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    μ.colLen c.val.2 = c.val.1 + 1 := by
  have hlt : c.val.1 < μ.colLen c.val.2 := by
    simpa using
      (YoungDiagram.mem_iff_lt_colLen (μ := μ) (i := c.val.1) (j := c.val.2)).mp
        c.property
  apply le_antisymm
  · by_contra hle
    have hgt : c.val.1 + 1 < μ.colLen c.val.2 := Nat.lt_of_not_ge hle
    let d : Cell μ := ⟨(c.val.1 + 1, c.val.2), by
      exact
        (YoungDiagram.mem_iff_lt_colLen (μ := μ) (i := c.val.1 + 1) (j := c.val.2)).mpr
          hgt⟩
    have hle_cd : CellLe c d := by
      change c.val.1 ≤ d.val.1 ∧ c.val.2 ≤ d.val.2
      simp [d]
    have hdc : d = c := hc d hle_cd
    have hval := congrArg Subtype.val hdc
    have hrow := congrArg Prod.fst hval
    change c.val.1 + 1 = c.val.1 at hrow
    omega
  · exact Nat.succ_le_of_lt hlt

/-- A cell is a corner exactly when it is the endpoint of its row and column. -/
theorem isCornerCell_iff_rowLen_colLen (μ : YoungDiagram) (c : Cell μ) :
    IsCornerCell μ c ↔
      μ.rowLen c.val.1 = c.val.2 + 1 ∧ μ.colLen c.val.2 = c.val.1 + 1 := by
  constructor
  · intro hc
    exact ⟨rowLen_corner μ c hc, colLen_corner μ c hc⟩
  · rintro ⟨hrow, hcol⟩ d hle
    apply Subtype.ext
    apply Prod.ext
    · have hdmem : (d.val.1, d.val.2) ∈ μ :=
        (YoungDiagram.mem_cells d.val).mp d.property
      have hleft : (d.val.1, c.val.2) ∈ μ :=
        μ.up_left_mem (le_rfl) hle.2 hdmem
      have hdlt : d.val.1 < μ.colLen c.val.2 :=
        YoungDiagram.mem_iff_lt_colLen.mp hleft
      have hdlt' : d.val.1 < c.val.1 + 1 := by
        simpa [hcol] using hdlt
      have hge : c.val.1 ≤ d.val.1 := hle.1
      omega
    · have hdmem : (d.val.1, d.val.2) ∈ μ :=
        (YoungDiagram.mem_cells d.val).mp d.property
      have hup : (c.val.1, d.val.2) ∈ μ :=
        μ.up_left_mem hle.1 (le_rfl) hdmem
      have hdlt : d.val.2 < μ.rowLen c.val.1 :=
        YoungDiagram.mem_iff_lt_rowLen.mp hup
      have hdlt' : d.val.2 < c.val.2 + 1 := by
        simpa [hrow] using hdlt
      have hge : c.val.2 ≤ d.val.2 := hle.2
      omega

/-- The last cell of a row whose length strictly drops in the next row. -/
def cornerCellOfRowDrop (μ : YoungDiagram) (i : ℕ)
    (hdrop : μ.rowLen (i + 1) < μ.rowLen i) : Cell μ :=
  ⟨(i, μ.rowLen i - 1), by
    apply (YoungDiagram.mem_cells (i, μ.rowLen i - 1)).mpr
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)⟩

/-- A strict row-length drop produces a corner at the end of that row. -/
theorem isCornerCell_cornerCellOfRowDrop (μ : YoungDiagram) (i : ℕ)
    (hdrop : μ.rowLen (i + 1) < μ.rowLen i) :
    IsCornerCell μ (cornerCellOfRowDrop μ i hdrop) := by
  let c := cornerCellOfRowDrop μ i hdrop
  have hrow : μ.rowLen c.val.1 = c.val.2 + 1 := by
    dsimp [c, cornerCellOfRowDrop]
    omega
  have hcol : μ.colLen c.val.2 = c.val.1 + 1 := by
    apply le_antisymm
    · by_contra hnot
      have hlt : c.val.1 + 1 < μ.colLen c.val.2 := Nat.lt_of_not_ge hnot
      have hcell : (c.val.1 + 1, c.val.2) ∈ μ :=
        YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have hjlt : c.val.2 < μ.rowLen (c.val.1 + 1) :=
        YoungDiagram.mem_iff_lt_rowLen.mp hcell
      dsimp [c, cornerCellOfRowDrop] at hjlt
      omega
    · have hcell : (c.val.1, c.val.2) ∈ μ :=
        (YoungDiagram.mem_cells c.val).mp c.property
      have hlt : c.val.1 < μ.colLen c.val.2 :=
        YoungDiagram.mem_iff_lt_colLen.mp hcell
      omega
  exact (isCornerCell_iff_rowLen_colLen μ c).mpr ⟨hrow, hcol⟩

/-- The row below a corner is strictly shorter than the corner's row. -/
theorem rowLen_succ_lt_rowLen_of_isCornerCell (μ : YoungDiagram)
    (c : Cell μ) (hc : IsCornerCell μ c) :
    μ.rowLen (c.val.1 + 1) < μ.rowLen c.val.1 := by
  have hrow := rowLen_corner μ c hc
  have hcol := colLen_corner μ c hc
  have hle : μ.rowLen (c.val.1 + 1) ≤ c.val.2 := by
    by_contra hnot
    have hlt : c.val.2 < μ.rowLen (c.val.1 + 1) := Nat.lt_of_not_ge hnot
    have hcell : (c.val.1 + 1, c.val.2) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hlt
    have hbad : c.val.1 + 1 < μ.colLen c.val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp hcell
    omega
  omega

/-- Finite row indices whose row length strictly drops in the next row. -/
def cornerRowIndices (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0)).filter fun i => μ.rowLen (i + 1) < μ.rowLen i

/-- Row-drop indices as a finite subtype. -/
abbrev CornerRows (μ : YoungDiagram) : Type :=
  {i : ℕ // i ∈ cornerRowIndices μ}

/-- Any row index above a removable row lies in the finite row range. -/
theorem rowIndex_mem_range_of_le_cornerRow (μ : YoungDiagram) (r : CornerRows μ)
    {i : ℕ} (hi : i ≤ r.1) :
    i ∈ Finset.range (μ.colLen 0) := by
  have hrange : r.1 ∈ Finset.range (μ.colLen 0) := (Finset.mem_filter.mp r.2).1
  exact Finset.mem_range.mpr (lt_of_le_of_lt hi (Finset.mem_range.mp hrange))

/-- Before a fixed removable row, membership in `cornerRowIndices` is exactly a row drop. -/
theorem mem_cornerRowIndices_iff_of_lt_cornerRow (μ : YoungDiagram) (r : CornerRows μ)
    {i : ℕ} (hi : i < r.1) :
    i ∈ cornerRowIndices μ ↔ μ.rowLen (i + 1) < μ.rowLen i := by
  rw [cornerRowIndices, Finset.mem_filter]
  exact ⟨fun h => h.2,
    fun h => ⟨rowIndex_mem_range_of_le_cornerRow μ r (Nat.le_of_lt hi), h⟩⟩

/-- Removable corners are equivalent to strict row-length drops. -/
noncomputable def cornerRowsEquivCornerCells (μ : YoungDiagram) :
    CornerRows μ ≃ CornerCells μ where
  toFun r :=
    let hdrop : μ.rowLen (r.1 + 1) < μ.rowLen r.1 :=
      (Finset.mem_filter.mp r.2).2
    ⟨cornerCellOfRowDrop μ r.1 hdrop, isCornerCell_cornerCellOfRowDrop μ r.1 hdrop⟩
  invFun c :=
    ⟨c.1.val.1, by
      rw [cornerRowIndices, Finset.mem_filter]
      have hcell : (c.1.val.1, c.1.val.2) ∈ μ :=
        (YoungDiagram.mem_cells c.1.val).mp c.1.property
      have hrow0 : (c.1.val.1, 0) ∈ μ :=
        μ.up_left_mem (le_rfl) (Nat.zero_le _) hcell
      have hrange : c.1.val.1 ∈ Finset.range (μ.colLen 0) :=
        Finset.mem_range.mpr (YoungDiagram.mem_iff_lt_colLen.mp hrow0)
      exact ⟨hrange, rowLen_succ_lt_rowLen_of_isCornerCell μ c.1 c.2⟩⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [cornerCellOfRowDrop]
      have hrow := rowLen_corner μ c.1 c.2
      omega

/-- Transport a sum over removable corners to the finite row-drop index set. -/
theorem cornerRows_sum_comp_equiv {M : Type*} [AddCommMonoid M]
    (μ : YoungDiagram) (f : CornerCells μ → M) :
    (∑ r : CornerRows μ, f (cornerRowsEquivCornerCells μ r)) =
      ∑ c : CornerCells μ, f c := by
  exact Equiv.sum_comp (cornerRowsEquivCornerCells μ) f

/-- Finite row indices whose row-boundary cells are addable corners. -/
def addableRowIndices (μ : YoungDiagram) : Finset ℕ :=
  insert 0 ((cornerRowIndices μ).image fun i => i + 1)

/-- Addable row indices as a finite subtype. -/
abbrev AddableRows (μ : YoungDiagram) : Type :=
  {i : ℕ // i ∈ addableRowIndices μ}

/-- The top row boundary is always addable. -/
theorem zero_mem_addableRowIndices (μ : YoungDiagram) :
    0 ∈ addableRowIndices μ := by
  simp [addableRowIndices]

/-- The row below a removable corner is addable. -/
theorem cornerRow_succ_mem_addableRowIndices (μ : YoungDiagram) (r : CornerRows μ) :
    r.1 + 1 ∈ addableRowIndices μ := by
  simp [addableRowIndices, r.2]

/-- There is one more addable row boundary than removable corner row. -/
theorem addableRowIndices_card (μ : YoungDiagram) :
    (addableRowIndices μ).card = (cornerRowIndices μ).card + 1 := by
  have hnot : 0 ∉ (cornerRowIndices μ).image (fun i => i + 1) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _hi, hsucc⟩
    omega
  have hinj : Function.Injective (fun i : ℕ => i + 1) := by
    intro a b h
    change a + 1 = b + 1 at h
    omega
  rw [addableRowIndices, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective (cornerRowIndices μ) hinj]

/-- Sums over addable row indices split into the top row and successor corner rows. -/
theorem addableRowIndices_sum_eq_zero_add_succ
    (μ : YoungDiagram) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (addableRowIndices μ).sum f =
      f 0 + (cornerRowIndices μ).sum (fun i => f (i + 1)) := by
  have hnot : 0 ∉ (cornerRowIndices μ).image (fun i => i + 1) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _hi, hsucc⟩
    omega
  have hinj : Set.InjOn (fun i : ℕ => i + 1) (cornerRowIndices μ) := by
    intro a _ha b _hb h
    change a + 1 = b + 1 at h
    omega
  rw [addableRowIndices, Finset.sum_insert hnot, Finset.sum_image]
  exact hinj

/-- There is one more addable row boundary than removable corner. -/
theorem addableRows_card (μ : YoungDiagram) :
    Fintype.card (AddableRows μ) = Fintype.card (CornerRows μ) + 1 := by
  rw [Fintype.card_coe, Fintype.card_coe, addableRowIndices_card]

/-- Products over addable row indices split into the top row and successor corner rows. -/
theorem addableRowIndices_prod_eq_zero_mul_succ
    (μ : YoungDiagram) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (addableRowIndices μ).prod f =
      f 0 * (cornerRowIndices μ).prod (fun i => f (i + 1)) := by
  have hnot : 0 ∉ (cornerRowIndices μ).image (fun i => i + 1) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _hi, hsucc⟩
    omega
  have hinj : Set.InjOn (fun i : ℕ => i + 1) (cornerRowIndices μ) := by
    intro a _ha b _hb h
    change a + 1 = b + 1 at h
    omega
  rw [addableRowIndices, Finset.prod_insert hnot, Finset.prod_image hinj]

/-- Products over addable row subtypes are products over the underlying index finset. -/
theorem addableRows_prod_eq (μ : YoungDiagram) {M : Type*} [CommMonoid M]
    (f : ℕ → M) :
    (Finset.univ.prod fun a : AddableRows μ => f a.1) =
      (addableRowIndices μ).prod f := by
  rw [Finset.univ_eq_attach (addableRowIndices μ)]
  exact Finset.prod_attach (addableRowIndices μ) f

/-- Sums over addable row subtypes are sums over the underlying index finset. -/
theorem addableRows_sum_eq (μ : YoungDiagram) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (Finset.univ.sum fun a : AddableRows μ => f a.1) =
      (addableRowIndices μ).sum f := by
  rw [Finset.univ_eq_attach (addableRowIndices μ)]
  exact Finset.sum_attach (addableRowIndices μ) f

/-- Products over corner row subtypes are products over the underlying index finset. -/
theorem cornerRows_prod_eq (μ : YoungDiagram) {M : Type*} [CommMonoid M]
    (f : ℕ → M) :
    (Finset.univ.prod fun r : CornerRows μ => f r.1) =
      (cornerRowIndices μ).prod f := by
  rw [Finset.univ_eq_attach (cornerRowIndices μ)]
  exact Finset.prod_attach (cornerRowIndices μ) f

/-- Sums over corner row subtypes are sums over the underlying index finset. -/
theorem cornerRows_sum_eq (μ : YoungDiagram) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (Finset.univ.sum fun r : CornerRows μ => f r.1) =
      (cornerRowIndices μ).sum f := by
  rw [Finset.univ_eq_attach (cornerRowIndices μ)]
  exact Finset.sum_attach (cornerRowIndices μ) f

/-- Corner row indices are all strictly above the first zero row. -/
theorem cornerRowIndices_filter_lt_colLen_zero (μ : YoungDiagram) :
    (cornerRowIndices μ).filter (fun i => i < μ.colLen 0) = cornerRowIndices μ := by
  ext i
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hi
    exact ⟨hi, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩

/-- Products over corner rows except one row drop, rewritten on the underlying index finset. -/
theorem cornerRows_filter_ne_prod_eq (μ : YoungDiagram) (r : CornerRows μ)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod fun s => f s.1) =
      (((cornerRowIndices μ).filter fun i => i ≠ r.1).prod f) := by
  rw [Finset.univ_eq_attach (cornerRowIndices μ)]
  rw [show
      ((cornerRowIndices μ).attach.filter fun s : (cornerRowIndices μ) => s ≠ r) =
        ((cornerRowIndices μ).attach.filter fun s : (cornerRowIndices μ) => s.1 ≠ r.1) by
    apply Finset.filter_congr
    intro s _hs
    constructor
    · intro hneq heq
      exact hneq (Subtype.ext heq)
    · intro hneq hsr
      exact hneq (congrArg Subtype.val hsr)]
  rw [Finset.filter_attach (fun i : ℕ => i ≠ r.1)]
  rw [Finset.prod_map]
  exact Finset.prod_attach (((cornerRowIndices μ).filter fun i => i ≠ r.1)) f

/-- Products over corner rows except one row split into rows above and below it. -/
theorem cornerRowIndices_filter_ne_prod_eq_lt_mul_gt
    (μ : YoungDiagram) (r : CornerRows μ) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (((cornerRowIndices μ).filter fun i => i ≠ r.1).prod f) =
      (((cornerRowIndices μ).filter fun i => i < r.1).prod f) *
        (((cornerRowIndices μ).filter fun i => r.1 < i).prod f) := by
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨hi, hne⟩
      refine Or.elim (lt_or_gt_of_ne hne.symm) ?_ ?_
      · intro hlt
        exact Or.inr ⟨hi, hlt⟩
      · intro hgt
        exact Or.inl ⟨hi, hgt⟩
    · intro h
      rcases h with ⟨hi, hlt⟩ | ⟨hi, hgt⟩
      · exact ⟨hi, by omega⟩
      · exact ⟨hi, by omega⟩
  · rw [Finset.disjoint_left]
    intro i hlt hgt
    simp only [Finset.mem_filter] at hlt hgt
    omega

/-- Products over all corner rows split into rows above and at-or-below a fixed row. -/
theorem cornerRowIndices_prod_eq_lt_mul_ge
    (μ : YoungDiagram) (r : CornerRows μ) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (cornerRowIndices μ).prod f =
      (((cornerRowIndices μ).filter fun s => s < r.1).prod f) *
        (((cornerRowIndices μ).filter fun s => r.1 ≤ s).prod f) := by
  rw [← Finset.prod_union]
  · congr 1
    ext s
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      exact Or.elim (lt_or_ge s r.1) (fun hlt => Or.inl ⟨hs, hlt⟩)
        (fun hge => Or.inr ⟨hs, hge⟩)
    · intro h
      exact h.elim (fun hlt => hlt.1) (fun hge => hge.1)
  · rw [Finset.disjoint_left]
    intro s hslt hsge
    rw [Finset.mem_filter] at hslt hsge
    exact not_lt_of_ge hsge.2 hslt.2

/-- Extending a strict upper-bound filter by one appends the new boundary term if present. -/
theorem finset_filter_lt_succ_prod (s : Finset ℕ) {M : Type*} [CommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ((s.filter fun i => i < n + 1).prod f) =
      if n ∈ s then ((s.filter fun i => i < n).prod f) * f n
      else (s.filter fun i => i < n).prod f := by
  by_cases hn : n ∈ s
  · rw [if_pos hn]
    have hnotmem : n ∉ s.filter (fun i => i < n) := by simp
    have hfilter :
        s.filter (fun i => i < n + 1) = insert n (s.filter fun i => i < n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro h
        by_cases hi : i = n
        · exact Or.inl hi
        · exact Or.inr ⟨h.1, by omega⟩
      · intro h
        rcases h with rfl | ⟨his, hlt⟩
        · exact ⟨hn, by omega⟩
        · exact ⟨his, by omega⟩
    rw [hfilter, Finset.prod_insert hnotmem]
    rw [mul_comm]
  · rw [if_neg hn]
    have hfilter :
        s.filter (fun i => i < n + 1) = s.filter (fun i => i < n) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · intro h
        have hne : i ≠ n := by
          intro hieq
          subst i
          exact hn h.1
        exact ⟨h.1, by omega⟩
      · intro h
        exact ⟨h.1, by omega⟩
    rw [hfilter]

/--
A product telescope over an interval with selected drop indices left as
boundary factors.
-/
theorem prod_Ico_telescope_with_drops (drops : Finset ℕ) {M : Type*} [CommMonoid M]
    (N D : ℕ → M) :
    ∀ n : ℕ, (∀ i, i < n → i ∉ drops → D i = N (i + 1)) →
      ((Finset.Ico 0 n).prod N) *
          (N n * ((drops.filter fun i => i < n).prod D)) =
        ((Finset.Ico 0 n).prod D) *
          (N 0 * ((drops.filter fun i => i < n).prod (fun i => N (i + 1))))
  | 0, _ => by simp
  | n + 1, hcancel => by
      have hcancel_n : ∀ i, i < n → i ∉ drops → D i = N (i + 1) := by
        intro i hi hnot
        exact hcancel i (by omega) hnot
      have ih := prod_Ico_telescope_with_drops drops N D n hcancel_n
      simp only [← Finset.range_eq_Ico] at ih ⊢
      rw [Finset.prod_range_succ N n]
      rw [Finset.prod_range_succ D n]
      rw [finset_filter_lt_succ_prod drops D n]
      rw [finset_filter_lt_succ_prod drops (fun i => N (i + 1)) n]
      by_cases hn : n ∈ drops
      · simp [hn]
        calc
          ((Finset.range n).prod N * N n) *
              (N (n + 1) * ((drops.filter fun i => i < n).prod D * D n))
              = ((Finset.range n).prod N *
                  (N n * (drops.filter fun i => i < n).prod D)) *
                    (D n * N (n + 1)) := by ac_rfl
          _ = ((Finset.range n).prod D *
                  (N 0 * (drops.filter fun i => i < n).prod (fun i => N (i + 1)))) *
                    (D n * N (n + 1)) := by rw [ih]
          _ = ((Finset.range n).prod D * D n) *
                (N 0 * ((drops.filter fun i => i < n).prod (fun i => N (i + 1)) *
                  N (n + 1))) := by ac_rfl
      · simp [hn]
        have hd : D n = N (n + 1) := hcancel n (Nat.lt_succ_self n) hn
        rw [hd]
        calc
          ((Finset.range n).prod N * N n) *
              (N (n + 1) * (drops.filter fun i => i < n).prod D)
              = ((Finset.range n).prod N *
                  (N n * (drops.filter fun i => i < n).prod D)) * N (n + 1) := by
                ac_rfl
          _ = ((Finset.range n).prod D *
                  (N 0 * (drops.filter fun i => i < n).prod (fun i => N (i + 1)))) *
                N (n + 1) := by rw [ih]
          _ = ((Finset.range n).prod D * N (n + 1)) *
                (N 0 * (drops.filter fun i => i < n).prod (fun i => N (i + 1))) := by
                ac_rfl

/--
An additive telescope over an interval with selected drop indices left as
boundary terms.
-/
theorem sum_Ico_telescope_with_drops (drops : Finset ℕ) {A : Type*} [AddCommMonoid A]
    (N D : ℕ → A) :
    ∀ n : ℕ, (∀ i, i < n → i ∉ drops → D i = N (i + 1)) →
      ((Finset.Ico 0 n).sum N) + (N n + ((drops.filter fun i => i < n).sum D)) =
        ((Finset.Ico 0 n).sum D) +
          (N 0 + ((drops.filter fun i => i < n).sum (fun i => N (i + 1)))) := by
  intro n h
  have hp := prod_Ico_telescope_with_drops drops (M := Multiplicative A)
    (fun i => Multiplicative.ofAdd (N i))
    (fun i => Multiplicative.ofAdd (D i)) n ?_
  · simpa using congrArg Multiplicative.toAdd hp
  · intro i hi hnot
    exact congrArg Multiplicative.ofAdd (h i hi hnot)

/-- Sum of the first `n` odd natural numbers. -/
theorem sum_range_odd (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2 := by
  have hsum : (Finset.range n).sum (fun i => 2 * i + 1) =
      2 * (Finset.range n).sum (fun i => i) + n := by
    rw [Finset.sum_add_distrib]
    rw [show (Finset.range n).sum (fun x => 2 * x) =
        2 * (Finset.range n).sum (fun i => i) by
      rw [← Finset.mul_sum]]
    simp [Finset.sum_const]
  have hid := Finset.sum_range_id_mul_two n
  rw [hsum]
  calc
    2 * (Finset.range n).sum (fun i => i) + n =
        (Finset.range n).sum (fun i => i) * 2 + n := by ring
    _ = n * (n - 1) + n := by rw [hid]
    _ = n ^ 2 := by
      cases n <;> simp [pow_two]
      ring

/-- Coefficients after multiplying a polynomial by `X - a`. -/
theorem coeff_X_sub_C_mul_rat (P : ℚ[X]) (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    ((Polynomial.X - Polynomial.C a) * P).coeff n =
      P.coeff (n - 1) - a * P.coeff n := by
  cases n with
  | zero => omega
  | succ k =>
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      simp [sub_eq_add_neg]

/-- The second leading coefficient of a product of rational linear factors. -/
theorem prod_X_sub_C_coeff_card_sub_two_rat {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) (hs : 2 ≤ s.card) :
    (2 : ℚ) * (∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))).coeff (s.card - 2) =
      (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 := by
  classical
  revert hs
  refine Finset.induction_on s ?empty ?insert
  · intro hs
    simp at hs
  · intro a s ha ih hs
    have hcard_insert : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    by_cases hscard1 : s.card = 1
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hscard1
      subst s
      simp only [Finset.mem_singleton] at ha
      rw [Finset.prod_insert, Finset.prod_singleton, hcard_insert]
      · simp [ha, pow_two]
        ring
      · simpa using ha
    · have hs_old : 2 ≤ s.card := by
        have hpos : 0 < s.card := by
          by_contra hle
          have hzero : s.card = 0 := by omega
          simp [hcard_insert, hzero] at hs
        omega
      have ihs := ih hs_old
      rw [Finset.prod_insert ha]
      rw [hcard_insert]
      have hidx : s.card + 1 - 2 = s.card - 1 := by omega
      rw [hidx]
      have hcoeff := coeff_X_sub_C_mul_rat ((∏ x ∈ s, (Polynomial.X - Polynomial.C (f x))))
        (f a) (n := s.card - 1) (by omega)
      rw [hcoeff]
      have hidx2 : s.card - 1 - 1 = s.card - 2 := by omega
      rw [hidx2]
      have hlead :
          (∏ x ∈ s, (Polynomial.X - Polynomial.C (f x))).coeff (s.card - 1) =
            -∑ x ∈ s, f x := by
        exact Polynomial.prod_X_sub_C_coeff_card_pred s f (by omega)
      rw [hlead]
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]
      ring_nf at ihs ⊢
      nlinarith

/-- A rational product of factors `X - c` is monic of degree the finset size. -/
theorem prod_X_sub_C_isMonicOfDegree_rat {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) :
    Polynomial.IsMonicOfDegree (∏ i ∈ s, (Polynomial.X - Polynomial.C (f i))) s.card := by
  refine (Polynomial.isMonicOfDegree_iff _ _).mpr ⟨?_, ?_⟩
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  · simpa [Polynomial.natDegree_finsetProd_X_sub_C_eq_card] using
      (Polynomial.monic_prod_X_sub_C f s).coeff_natDegree

/--
Lagrange coefficient identity for one more numerator node than denominator
node, in the form used by addable/removable contents.
-/
theorem lagrange_sum_prod_div_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (y : α → ℚ) (x : β → ℚ)
    (hB : B.Nonempty) (hcard : A.card = B.card + 1)
    (hinj : Set.InjOn x B)
    (hsum : (A.sum y) = B.sum x) :
    B.sum (fun i => (A.prod (fun a => x i - y a)) /
      ((B.erase i).prod (fun j => x i - x j))) =
        ((B.sum (fun i => x i ^ 2)) - (A.sum (fun a => y a ^ 2))) / 2 := by
  classical
  let PA : ℚ[X] := ∏ a ∈ A, (Polynomial.X - Polynomial.C (y a))
  let QB : ℚ[X] := ∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))
  let R : ℚ[X] := PA - Polynomial.X * QB
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB
  have hApos : 0 < A.card := by omega
  have hA2 : 2 ≤ A.card := by omega
  have hPAimd : Polynomial.IsMonicOfDegree PA A.card := by
    dsimp [PA]
    exact prod_X_sub_C_isMonicOfDegree_rat A y
  have hQBimd : Polynomial.IsMonicOfDegree QB B.card := by
    dsimp [QB]
    exact prod_X_sub_C_isMonicOfDegree_rat B x
  have hXQimd : Polynomial.IsMonicOfDegree (Polynomial.X * QB) A.card := by
    rw [hcard]
    simpa [Nat.add_comm] using (Polynomial.isMonicOfDegree_X (R := ℚ)).mul hQBimd
  have hRnat : R.natDegree < A.card := by
    dsimp [R]
    exact Polynomial.IsMonicOfDegree.natDegree_sub_lt (by omega) hPAimd hXQimd
  have hRdeg : R.degree < B.card := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    by_cases hn_eq : n = B.card
    · subst n
      dsimp [R, PA, QB]
      rw [Polynomial.coeff_sub]
      have hPAcoeff :
          (∏ a ∈ A, (Polynomial.X - Polynomial.C (y a))).coeff B.card =
            -∑ a ∈ A, y a := by
        have hidx : B.card = A.card - 1 := by omega
        rw [hidx]
        exact Polynomial.prod_X_sub_C_coeff_card_pred A y hApos
      rw [hPAcoeff]
      have hXQcoeff :
          (Polynomial.X * ∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))).coeff B.card =
            -∑ i ∈ B, x i := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hBpos)
        rw [hk]
        rw [Polynomial.coeff_X_mul]
        have hcardk : B.card - 1 = k := by omega
        rw [← hcardk]
        exact Polynomial.prod_X_sub_C_coeff_card_pred B x hBpos
      rw [hXQcoeff]
      rw [hsum]
      ring
    · have hAn : A.card ≤ n := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hRnat hAn)
  have hinterp := QuantumOracle.HookLengthCompat.coeff_eq_sum (s := B) (v := x) (P := R) hinj hRdeg
  have hRcoeff : R.coeff (B.card - 1) =
      ((B.sum (fun i => x i ^ 2)) - (A.sum (fun a => y a ^ 2))) / 2 := by
    dsimp [R, PA, QB]
    rw [Polynomial.coeff_sub]
    have hPA2 : (2 : ℚ) *
        (∏ a ∈ A, (Polynomial.X - Polynomial.C (y a))).coeff (B.card - 1) =
          (A.sum y) ^ 2 - A.sum (fun a => y a ^ 2) := by
      have hidx : B.card - 1 = A.card - 2 := by omega
      rw [hidx]
      exact prod_X_sub_C_coeff_card_sub_two_rat A y hA2
    by_cases hBcard1 : B.card = 1
    · have hXQ0 :
          (Polynomial.X * ∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))).coeff
              (B.card - 1) = 0 := by
        rw [hBcard1]
        simp
      rw [hXQ0]
      have hBsq : (B.sum x) ^ 2 = B.sum (fun i => x i ^ 2) := by
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard1
        subst B
        simp [pow_two]
      rw [← hBsq, ← hsum]
      linarith
    · have hB2 : 2 ≤ B.card := by omega
      have hXQ2 : (2 : ℚ) *
          (Polynomial.X * ∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))).coeff
              (B.card - 1) =
            (B.sum x) ^ 2 - B.sum (fun i => x i ^ 2) := by
        have hcoeff :
            (Polynomial.X * ∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))).coeff
                (B.card - 1) =
              (∏ i ∈ B, (Polynomial.X - Polynomial.C (x i))).coeff (B.card - 2) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B.card - 1 ≠ 0)
          rw [hk]
          rw [Polynomial.coeff_X_mul]
          have hidx : k = B.card - 2 := by omega
          rw [hidx]
        rw [hcoeff]
        exact prod_X_sub_C_coeff_card_sub_two_rat B x hB2
      rw [hsum] at hPA2
      linarith
  rw [hinterp] at hRcoeff
  rw [← hRcoeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hReval : R.eval (x i) = A.prod (fun a => x i - y a) := by
    dsimp [R, PA, QB]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    have hQzero : Polynomial.eval (x i)
        (∏ j ∈ B, (Polynomial.X - Polynomial.C (x j))) = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero hi
      simp
    rw [hQzero]
    simp [Polynomial.eval_prod]
  rw [hReval]

/-- In a row-affected cell, the erased corner lies in the row slice of that cell's hook. -/
theorem corner_mem_hookRowCells_of_mem_hookAffectedRowCells (μ : YoungDiagram)
    (c d : Cell μ) (h : d ∈ hookAffectedRowCells μ c) :
    c.val ∈ hookRowCells μ d := by
  simp [hookAffectedRowCells] at h
  simp [hookRowCells, YoungDiagram.mem_row_iff, h.1, le_of_lt h.2]

/-- In a row-affected cell, the erased corner is not in the column slice of that cell's hook. -/
theorem corner_not_mem_hookColCells_of_mem_hookAffectedRowCells (μ : YoungDiagram)
    (c d : Cell μ) (h : d ∈ hookAffectedRowCells μ c) :
    c.val ∉ hookColCells μ d := by
  simp [hookAffectedRowCells] at h
  simp [hookColCells, YoungDiagram.mem_col_iff]
  omega

/--
For a row-affected cell, decrementing the hook length erases the corner from
the row slice and leaves the column slice cardinal unchanged.
-/
theorem hookLength_sub_one_eq_row_erase_card_add_col_card_sub_one_of_mem_hookAffectedRowCells
    (μ : YoungDiagram) (c d : Cell μ) (h : d ∈ hookAffectedRowCells μ c) :
    hookLength μ d - 1 =
      ((hookRowCells μ d).erase c.val).card + (hookColCells μ d).card - 1 := by
  have hrowmem : c.val ∈ hookRowCells μ d :=
    corner_mem_hookRowCells_of_mem_hookAffectedRowCells μ c d h
  have hrowcard :
      (hookRowCells μ d).card = ((hookRowCells μ d).erase c.val).card + 1 := by
    rw [eq_comm]
    exact Finset.card_erase_add_one hrowmem
  have hcolpos : 0 < (hookColCells μ d).card :=
    Finset.card_pos.mpr ⟨d.val, mem_hookColCells_self μ d⟩
  rw [hookLength_eq_row_card_add_col_card_sub_one, hrowcard]
  omega

/-- In a column-affected cell, the erased corner lies in the column slice of that cell's hook. -/
theorem corner_mem_hookColCells_of_mem_hookAffectedColCells (μ : YoungDiagram)
    (c d : Cell μ) (h : d ∈ hookAffectedColCells μ c) :
    c.val ∈ hookColCells μ d := by
  simp [hookAffectedColCells] at h
  simp [hookColCells, YoungDiagram.mem_col_iff, h.1, le_of_lt h.2]

/-- In a column-affected cell, the erased corner is not in the row slice of that cell's hook. -/
theorem corner_not_mem_hookRowCells_of_mem_hookAffectedColCells (μ : YoungDiagram)
    (c d : Cell μ) (h : d ∈ hookAffectedColCells μ c) :
    c.val ∉ hookRowCells μ d := by
  simp [hookAffectedColCells] at h
  simp [hookRowCells, YoungDiagram.mem_row_iff]
  omega

/--
For a column-affected cell, decrementing the hook length erases the corner
from the column slice and leaves the row slice cardinal unchanged.
-/
theorem hookLength_sub_one_eq_row_card_add_col_erase_card_sub_one_of_mem_hookAffectedColCells
    (μ : YoungDiagram) (c d : Cell μ) (h : d ∈ hookAffectedColCells μ c) :
    hookLength μ d - 1 =
      (hookRowCells μ d).card + ((hookColCells μ d).erase c.val).card - 1 := by
  have hcolmem : c.val ∈ hookColCells μ d :=
    corner_mem_hookColCells_of_mem_hookAffectedColCells μ c d h
  have hcolcard :
      (hookColCells μ d).card = ((hookColCells μ d).erase c.val).card + 1 := by
    rw [eq_comm]
    exact Finset.card_erase_add_one hcolmem
  have hrowpos : 0 < (hookRowCells μ d).card :=
    Finset.card_pos.mpr ⟨d.val, mem_hookRowCells_self μ d⟩
  rw [hookLength_eq_row_card_add_col_card_sub_one, hcolcard]
  omega

/-- Rewrite the affected decremented hook product using row and column slice cardinalities. -/
theorem hookAffectedCells_prod_hookLength_sub_one_eq_row_col_slice_products
    (μ : YoungDiagram) (c : Cell μ) :
    (hookAffectedCells μ c).prod (fun d => hookLength μ d - 1) =
      (hookAffectedRowCells μ c).prod
          (fun d => ((hookRowCells μ d).erase c.val).card + (hookColCells μ d).card - 1) *
        (hookAffectedColCells μ c).prod
          (fun d => (hookRowCells μ d).card + ((hookColCells μ d).erase c.val).card - 1) := by
  rw [hookAffectedCells_prod_eq_row_mul_col]
  congr 1
  · apply Finset.prod_congr rfl
    intro d hd
    exact
      hookLength_sub_one_eq_row_erase_card_add_col_card_sub_one_of_mem_hookAffectedRowCells
        μ c d hd
  · apply Finset.prod_congr rfl
    intro d hd
    exact
      hookLength_sub_one_eq_row_card_add_col_erase_card_sub_one_of_mem_hookAffectedColCells
        μ c d hd

/-- The row part of an interval-indexed row-affected hook after erasing the corner. -/
theorem hookAffectedRowCellOfIndex_row_erase_card (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {j : ℕ} (hj : j ∈ Finset.Ico 0 c.val.2) :
    ((hookRowCells μ (hookAffectedRowCellOfIndex μ c j)).erase c.val).card =
      c.val.2 - j := by
  have hjlt : j < c.val.2 := (Finset.mem_Ico.mp hj).2
  have hmem : hookAffectedRowCellOfIndex μ c j ∈ hookAffectedRowCells μ c :=
    hookAffectedRowCellOfIndex_mem μ c hj
  have hcorner : c.val ∈ hookRowCells μ (hookAffectedRowCellOfIndex μ c j) :=
    corner_mem_hookRowCells_of_mem_hookAffectedRowCells μ c
      (hookAffectedRowCellOfIndex μ c j) hmem
  rw [Finset.card_erase_of_mem hcorner]
  rw [hookRowCells_card]
  rw [hookAffectedRowCellOfIndex_of_lt μ c hjlt]
  rw [rowLen_corner μ c hc]
  simp
  omega

/-- The column part of an interval-indexed row-affected hook. -/
theorem hookAffectedRowCellOfIndex_col_card (μ : YoungDiagram) (c : Cell μ)
    {j : ℕ} (hj : j ∈ Finset.Ico 0 c.val.2) :
    (hookColCells μ (hookAffectedRowCellOfIndex μ c j)).card =
      μ.colLen j - c.val.1 := by
  have hjlt : j < c.val.2 := (Finset.mem_Ico.mp hj).2
  rw [hookColCells_card]
  rw [hookAffectedRowCellOfIndex_of_lt μ c hjlt]

/-- The column part of an interval-indexed column-affected hook after erasing the corner. -/
theorem hookAffectedColCellOfIndex_col_erase_card (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {i : ℕ} (hi : i ∈ Finset.Ico 0 c.val.1) :
    ((hookColCells μ (hookAffectedColCellOfIndex μ c i)).erase c.val).card =
      c.val.1 - i := by
  have hilt : i < c.val.1 := (Finset.mem_Ico.mp hi).2
  have hmem : hookAffectedColCellOfIndex μ c i ∈ hookAffectedColCells μ c :=
    hookAffectedColCellOfIndex_mem μ c hi
  have hcorner : c.val ∈ hookColCells μ (hookAffectedColCellOfIndex μ c i) :=
    corner_mem_hookColCells_of_mem_hookAffectedColCells μ c
      (hookAffectedColCellOfIndex μ c i) hmem
  rw [Finset.card_erase_of_mem hcorner]
  rw [hookColCells_card]
  rw [hookAffectedColCellOfIndex_of_lt μ c hilt]
  rw [colLen_corner μ c hc]
  simp
  omega

/-- The row part of an interval-indexed column-affected hook. -/
theorem hookAffectedColCellOfIndex_row_card (μ : YoungDiagram) (c : Cell μ)
    {i : ℕ} (hi : i ∈ Finset.Ico 0 c.val.1) :
    (hookRowCells μ (hookAffectedColCellOfIndex μ c i)).card =
      μ.rowLen i - c.val.2 := by
  have hilt : i < c.val.1 := (Finset.mem_Ico.mp hi).2
  rw [hookRowCells_card]
  rw [hookAffectedColCellOfIndex_of_lt μ c hilt]

/-- Row-affected decremented hook factors as an interval product. -/
theorem hookAffectedRowCells_prod_slice_factors_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    (hookAffectedRowCells μ c).prod
        (fun d => ((hookRowCells μ d).erase c.val).card + (hookColCells μ d).card - 1) =
      (Finset.Ico 0 c.val.2).prod
        (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1) - 1) := by
  rw [hookAffectedRowCells_prod_eq_Ico]
  apply Finset.prod_congr rfl
  intro j hj
  rw [hookAffectedRowCellOfIndex_row_erase_card μ c hc hj,
    hookAffectedRowCellOfIndex_col_card μ c hj]

/-- Column-affected decremented hook factors as an interval product. -/
theorem hookAffectedColCells_prod_slice_factors_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    (hookAffectedColCells μ c).prod
        (fun d => (hookRowCells μ d).card + ((hookColCells μ d).erase c.val).card - 1) =
      (Finset.Ico 0 c.val.1).prod
        (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i) - 1) := by
  rw [hookAffectedColCells_prod_eq_Ico]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hookAffectedColCellOfIndex_row_card μ c hi,
    hookAffectedColCellOfIndex_col_erase_card μ c hc hi]

/-- Affected decremented hook factors as explicit row and column interval products. -/
theorem hookAffectedCells_prod_hookLength_sub_one_eq_interval_products
    (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (hookAffectedCells μ c).prod (fun d => hookLength μ d - 1) =
      (Finset.Ico 0 c.val.2).prod
          (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1) - 1) *
        (Finset.Ico 0 c.val.1).prod
          (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i) - 1) := by
  rw [hookAffectedCells_prod_hookLength_sub_one_eq_row_col_slice_products]
  rw [hookAffectedRowCells_prod_slice_factors_eq_Ico μ c hc,
    hookAffectedColCells_prod_slice_factors_eq_Ico μ c hc]

/-- Hook length of an interval-indexed row-affected cell. -/
theorem hookAffectedRowCellOfIndex_hookLength (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {j : ℕ} (hj : j ∈ Finset.Ico 0 c.val.2) :
    hookLength μ (hookAffectedRowCellOfIndex μ c j) =
      (c.val.2 - j) + (μ.colLen j - c.val.1) := by
  have hjlt : j < c.val.2 := (Finset.mem_Ico.mp hj).2
  have hjcell := hookAffectedRowCellOfIndex_of_lt μ c hjlt
  rw [hookLength_eq_rowLen_sub_add_colLen_sub_sub_one]
  rw [hjcell]
  rw [rowLen_corner μ c hc]
  simp
  omega

/-- Hook length of an interval-indexed column-affected cell. -/
theorem hookAffectedColCellOfIndex_hookLength (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {i : ℕ} (hi : i ∈ Finset.Ico 0 c.val.1) :
    hookLength μ (hookAffectedColCellOfIndex μ c i) =
      (μ.rowLen i - c.val.2) + (c.val.1 - i) := by
  have hilt : i < c.val.1 := (Finset.mem_Ico.mp hi).2
  have hicell := hookAffectedColCellOfIndex_of_lt μ c hilt
  rw [hookLength_eq_rowLen_sub_add_colLen_sub_sub_one]
  rw [hicell]
  rw [colLen_corner μ c hc]
  simp
  omega

/-- Row-affected original hook factors as an interval product. -/
theorem hookAffectedRowCells_prod_hookLength_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    (hookAffectedRowCells μ c).prod (fun d => hookLength μ d) =
      (Finset.Ico 0 c.val.2).prod
        (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1)) := by
  rw [hookAffectedRowCells_prod_eq_Ico]
  apply Finset.prod_congr rfl
  intro j hj
  rw [hookAffectedRowCellOfIndex_hookLength μ c hc hj]

/-- Column-affected original hook factors as an interval product. -/
theorem hookAffectedColCells_prod_hookLength_eq_Ico (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    (hookAffectedColCells μ c).prod (fun d => hookLength μ d) =
      (Finset.Ico 0 c.val.1).prod
        (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i)) := by
  rw [hookAffectedColCells_prod_eq_Ico]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hookAffectedColCellOfIndex_hookLength μ c hc hi]

/-- Affected original hook factors as explicit row and column interval products. -/
theorem hookAffectedCells_prod_hookLength_eq_interval_products
    (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (hookAffectedCells μ c).prod (fun d => hookLength μ d) =
      (Finset.Ico 0 c.val.2).prod
          (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1)) *
        (Finset.Ico 0 c.val.1).prod
          (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i)) := by
  rw [hookAffectedCells_prod_eq_row_mul_col]
  rw [hookAffectedRowCells_prod_hookLength_eq_Ico μ c hc,
    hookAffectedColCells_prod_hookLength_eq_Ico μ c hc]

/-- Hook lengths are positive because each hook contains its base cell. -/
theorem hookLength_pos (μ : YoungDiagram) (c : Cell μ) : 0 < hookLength μ c := by
  rw [hookLength]
  exact Finset.card_pos.mpr ⟨c.val, mem_hookCells_self μ c⟩

/-- A removable corner has no hook cells except itself. -/
theorem hookCells_corner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    hookCells μ c = {c.val} := by
  ext p
  constructor
  · intro hp
    rw [hookCells] at hp
    simp only [Finset.mem_filter] at hp
    rcases hp with ⟨hpmem, hhook⟩
    have hcell_eq : (⟨p, hpmem⟩ : Cell μ) = c := by
      apply hc
      rcases hhook with hrow | hcol
      · constructor
        · rw [hrow.1]
        · exact hrow.2
      · constructor
        · exact hcol.2
        · rw [hcol.1]
    exact Finset.mem_singleton.mpr (congrArg Subtype.val hcell_eq)
  · intro hp
    rw [Finset.mem_singleton] at hp
    subst p
    exact mem_hookCells_self μ c

/-- The hook length of a removable corner is one. -/
theorem hookLength_corner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    hookLength μ c = 1 := by
  rw [hookLength, hookCells_corner μ c hc]
  simp

/-- The hook of an erased-shape cell is the original hook with the erased corner removed. -/
theorem hookCells_eraseCorner (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c)
    (d : Cell (eraseCorner μ c hc)) :
    hookCells (eraseCorner μ c hc) d =
      (hookCells μ (eraseCornerCellEmbedding μ c hc d)).erase c.val := by
  ext p
  simp [hookCells, eraseCornerCellEmbedding_apply_val, and_assoc]

/--
If the removed corner was in a remaining cell's hook, then that hook length
drops by exactly one.
-/
theorem hookLength_eraseCorner_add_one_of_mem (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc))
    (hmem : c.val ∈ hookCells μ (eraseCornerCellEmbedding μ c hc d)) :
    hookLength (eraseCorner μ c hc) d + 1 =
      hookLength μ (eraseCornerCellEmbedding μ c hc d) := by
  rw [hookLength, hookCells_eraseCorner, hookLength]
  exact Finset.card_erase_add_one hmem

/--
If the removed corner was not in a remaining cell's hook, then that hook length
is unchanged.
-/
theorem hookLength_eraseCorner_of_not_mem (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc))
    (hmem : c.val ∉ hookCells μ (eraseCornerCellEmbedding μ c hc d)) :
    hookLength (eraseCorner μ c hc) d =
      hookLength μ (eraseCornerCellEmbedding μ c hc d) := by
  rw [hookLength, hookCells_eraseCorner, hookLength]
  rw [Finset.erase_eq_of_notMem hmem]

/-- Erasing a corner can only weakly decrease hook lengths of remaining cells. -/
theorem hookLength_eraseCorner_le (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) (d : Cell (eraseCorner μ c hc)) :
    hookLength (eraseCorner μ c hc) d ≤
      hookLength μ (eraseCornerCellEmbedding μ c hc d) := by
  rw [hookLength, hookCells_eraseCorner, hookLength]
  exact Finset.card_erase_le

/-- A standard tableau as a bijective, product-order-preserving filling by `0, ..., μ.card - 1`. -/
def IsStandardTableau (μ : YoungDiagram) (T : Cell μ → Fin μ.card) : Prop :=
  Function.Bijective T ∧ ∀ a b : Cell μ, CellLe a b → a ≠ b → T a < T b

/-- The finite type of standard tableaux of shape `μ`. -/
abbrev StandardTableaux (μ : YoungDiagram) : Type :=
  {T : Cell μ → Fin μ.card // IsStandardTableau μ T}

/-- Row-and-column version of the standard-tableau predicate, kept as a convention-facing target. -/
def IsStandardTableauRowsCols (μ : YoungDiagram) (T : Cell μ → Fin μ.card) : Prop :=
  Function.Bijective T ∧
    (∀ a b : Cell μ, a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a < T b) ∧
      (∀ a b : Cell μ, a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)

/-- A tableau has a maximum entry at the chosen cell. -/
def IsMaxEntryAt {μ : YoungDiagram} (T : Cell μ → Fin μ.card) (c : Cell μ) : Prop :=
  ∀ d : Cell μ, T d ≤ T c

/-- Standard tableaux tagged by the unique corner carrying their maximum entry. -/
abbrev MaxCornerStandardTableaux (μ : YoungDiagram) : Type :=
  {p : Cell μ × (Cell μ → Fin μ.card) //
    IsCornerCell μ p.1 ∧ IsStandardTableau μ p.2 ∧ IsMaxEntryAt p.2 p.1}

/-- Standard tableaux whose maximum entry is at a fixed corner. -/
abbrev FixedMaxStandardTableaux (μ : YoungDiagram) (c : CornerCells μ) : Type :=
  {T : Cell μ → Fin μ.card // IsStandardTableau μ T ∧ IsMaxEntryAt T c.1}

/-- An injective filling has at most one cell carrying a maximum entry. -/
theorem isMaxEntryAt_unique {μ : YoungDiagram} {T : Cell μ → Fin μ.card}
    (hTinj : Function.Injective T) {c d : Cell μ}
    (hcmax : IsMaxEntryAt T c) (hdmax : IsMaxEntryAt T d) :
    c = d := by
  apply hTinj
  exact le_antisymm (hdmax c) (hcmax d)

/-- A standard tableau has at most one cell carrying a maximum entry. -/
theorem isMaxEntryAt_unique_of_standard {μ : YoungDiagram} {T : Cell μ → Fin μ.card}
    (hT : IsStandardTableau μ T) {c d : Cell μ}
    (hcmax : IsMaxEntryAt T c) (hdmax : IsMaxEntryAt T d) :
    c = d :=
  isMaxEntryAt_unique hT.1.1 hcmax hdmax

/-- Restricting and relabelling a standard tableau after erasing a corner stays standard. -/
theorem isStandardTableau_eraseCornerRestrict (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hT : IsStandardTableau μ T) :
    IsStandardTableau (eraseCorner μ c hc)
      (eraseCornerRestrictTableau μ c hc hT.1.1) := by
  refine ⟨eraseCornerRestrictTableau_bijective μ c hc hT.1.1, ?_⟩
  intro a b hab hne
  have hle_emb : CellLe (eraseCornerCellEmbedding μ c hc a)
      (eraseCornerCellEmbedding μ c hc b) := by
    simpa [CellLe, eraseCornerCellEmbedding_apply_val] using hab
  have hne_emb : eraseCornerCellEmbedding μ c hc a ≠ eraseCornerCellEmbedding μ c hc b := by
    intro h
    exact hne ((eraseCornerCellEmbedding μ c hc).injective h)
  have hlt_old : T (eraseCornerCellEmbedding μ c hc a) <
      T (eraseCornerCellEmbedding μ c hc b) :=
    hT.2 _ _ hle_emb hne_emb
  have hlt_cast :
      Fin.cast (eraseCorner_card_add_one μ c hc).symm
          (T (eraseCornerCellEmbedding μ c hc a)) <
        Fin.cast (eraseCorner_card_add_one μ c hc).symm
          (T (eraseCornerCellEmbedding μ c hc b)) := by
    simpa using hlt_old
  have hsucc_lt :
      (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
          (eraseCornerRelabelValue μ c hc hT.1.1 a) <
        (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
          (eraseCornerRelabelValue μ c hc hT.1.1 b) := by
    rw [succAbove_eraseCornerRelabelValue, succAbove_eraseCornerRelabelValue]
    exact hlt_cast
  exact Fin.succAbove_lt_succAbove_iff.mp hsucc_lt

/-- Extend a tableau on an erased-corner shape by inserting the corner with the top value. -/
noncomputable def insertCornerTableau (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c)
    (T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card) :
    Cell μ → Fin μ.card :=
  fun d ↦
    Fin.cast (eraseCorner_card_add_one μ c hc) <|
      if h : d = c then Fin.last (eraseCorner μ c hc).card
      else (T (eraseCornerCellOfNe μ c hc d h)).castSucc

/-- Inserting a corner with the top value is injective when the smaller filling is injective. -/
theorem insertCornerTableau_injective (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c)
    {T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card}
    (hTinj : Function.Injective T) :
    Function.Injective (insertCornerTableau μ c hc T) := by
  intro a b hab
  by_cases ha : a = c
  · subst a
    by_cases hb : b = c
    · exact hb.symm
    · have hcast := Fin.cast_injective (eraseCorner_card_add_one μ c hc) hab
      simp [hb] at hcast
      exact False.elim ((Fin.castSucc_ne_last _) hcast.symm)
  · by_cases hb : b = c
    · subst b
      have hcast := Fin.cast_injective (eraseCorner_card_add_one μ c hc) hab
      simp [ha] at hcast
    · have hcast := Fin.cast_injective (eraseCorner_card_add_one μ c hc) hab
      simp [ha, hb] at hcast
      have hcell : eraseCornerCellOfNe μ c hc a ha = eraseCornerCellOfNe μ c hc b hb :=
        hTinj hcast
      have hemb := congrArg (eraseCornerCellEmbedding μ c hc) hcell
      simpa using hemb

/-- Inserting a corner with the top value is bijective when the smaller filling is injective. -/
theorem insertCornerTableau_bijective (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c)
    {T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card}
    (hTinj : Function.Injective T) :
    Function.Bijective (insertCornerTableau μ c hc T) := by
  refine ⟨insertCornerTableau_injective μ c hc hTinj, ?_⟩
  have hcard : Fintype.card (Cell μ) = Fintype.card (Fin μ.card) := by
    rw [cell_fintype_card, Fintype.card_fin]
  exact (insertCornerTableau_injective μ c hc hTinj).surjective_of_finite
    (Fintype.equivOfCardEq hcard)

/-- Inserting a corner with the top value preserves standard tableaux. -/
theorem isStandardTableau_insertCorner (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c)
    {T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card}
    (hT : IsStandardTableau (eraseCorner μ c hc) T) :
    IsStandardTableau μ (insertCornerTableau μ c hc T) := by
  refine ⟨insertCornerTableau_bijective μ c hc hT.1.1, ?_⟩
  intro a b hab hne
  by_cases ha : a = c
  · subst a
    exact False.elim (hne ((hc b hab).symm))
  · by_cases hb : b = c
    · subst b
      simp [insertCornerTableau, ha]
    · have hle_erased : CellLe (eraseCornerCellOfNe μ c hc a ha)
          (eraseCornerCellOfNe μ c hc b hb) := by
        simpa [CellLe, eraseCornerCellOfNe] using hab
      have hne_erased : eraseCornerCellOfNe μ c hc a ha ≠
          eraseCornerCellOfNe μ c hc b hb := by
        intro h
        have hemb := congrArg (eraseCornerCellEmbedding μ c hc) h
        exact hne (by simpa using hemb)
      have hlt_old : T (eraseCornerCellOfNe μ c hc a ha) <
          T (eraseCornerCellOfNe μ c hc b hb) :=
        hT.2 _ _ hle_erased hne_erased
      simpa [insertCornerTableau, ha, hb] using hlt_old

/--
The product-order standard-tableau predicate is equivalent to the usual
row-and-column strictness formulation for bijective tableaux.
-/
theorem isStandardTableau_iff_rowsCols (μ : YoungDiagram) (T : Cell μ → Fin μ.card) :
    IsStandardTableau μ T ↔ IsStandardTableauRowsCols μ T := by
  constructor
  · intro h
    rcases h with ⟨hbij, hmono⟩
    refine ⟨hbij, ?_, ?_⟩
    · intro a b hrow hcol
      exact hmono a b ⟨le_of_eq hrow, le_of_lt hcol⟩ (by
        intro hab
        cases hab
        omega)
    · intro a b hcol hi
      exact hmono a b ⟨le_of_lt hi, le_of_eq hcol⟩ (by
        intro hab
        cases hab
        omega)
  · intro h
    rcases h with ⟨hbij, hrow, hcol⟩
    refine ⟨hbij, ?_⟩
    intro a b hle hne
    rcases hle with ⟨hi_le, hj_le⟩
    rcases lt_or_eq_of_le hi_le with hi | hi
    · rcases lt_or_eq_of_le hj_le with hj | hj
      · let m : Cell μ :=
          ⟨(b.val.1, a.val.2), by
            have hb : (b.val.1, b.val.2) ∈ μ := by
              exact b.property
            have hm : (b.val.1, a.val.2) ∈ μ :=
              μ.up_left_mem (by rfl) hj_le hb
            exact hm⟩
        exact lt_trans (hcol a m (by rfl) hi) (hrow m b (by rfl) hj)
      · exact hcol a b hj hi
    · rcases lt_or_eq_of_le hj_le with hj | hj
      · exact hrow a b hi hj
      · exfalso
        apply hne
        apply Subtype.ext
        exact Prod.ext hi hj

/--
If a filling is surjective and `c` carries a maximum value, then `c` carries
the top value written in the cardinality coordinates of `eraseCorner μ c hc`.
-/
theorem tableau_max_value_eq_inserted_top (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hTsurj : Function.Surjective T) (hcmax : ∀ d : Cell μ, T d ≤ T c) :
    T c = Fin.cast (eraseCorner_card_add_one μ c hc)
      (Fin.last (eraseCorner μ c hc).card) := by
  let top : Fin μ.card :=
    Fin.cast (eraseCorner_card_add_one μ c hc)
      (Fin.last (eraseCorner μ c hc).card)
  have hc_le_top : T c ≤ top := by
    have hcast :
        Fin.cast (eraseCorner_card_add_one μ c hc)
          (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)) ≤ top := by
      exact (Fin.cast_le_cast (eraseCorner_card_add_one μ c hc)).mpr (Fin.le_last _)
    simpa [top] using hcast
  obtain ⟨d, hd⟩ := hTsurj top
  have htop_le : top ≤ T c := by
    simpa [hd] using hcmax d
  exact le_antisymm hc_le_top htop_le

/-- A maximum-entry cell in a standard tableau carries the top value. -/
theorem standardTableau_max_value_eq_inserted_top (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hT : IsStandardTableau μ T) (hcmax : ∀ d : Cell μ, T d ≤ T c) :
    T c = Fin.cast (eraseCorner_card_add_one μ c hc)
      (Fin.last (eraseCorner μ c hc).card) :=
  tableau_max_value_eq_inserted_top μ c hc hT.1.2 hcmax

/-- An inserted tableau restricts back to the erased-shape tableau it came from. -/
theorem eraseCornerRestrict_insertCorner_eq (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c)
    {T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card}
    (hT : IsStandardTableau (eraseCorner μ c hc) T) :
    eraseCornerRestrictTableau μ c hc
      (insertCornerTableau_bijective μ c hc hT.1.1).1 = T := by
  funext d
  let hInsInj := (insertCornerTableau_bijective μ c hc hT.1.1).1
  have hpivot :
      Fin.cast (eraseCorner_card_add_one μ c hc).symm
          (insertCornerTableau μ c hc T c) =
        Fin.last (eraseCorner μ c hc).card := by
    simp [insertCornerTableau]
  have hvalue :
      Fin.cast (eraseCorner_card_add_one μ c hc).symm
          (insertCornerTableau μ c hc T (eraseCornerCellEmbedding μ c hc d)) =
        (T d).castSucc := by
    simp [insertCornerTableau, eraseCornerCellEmbedding_ne_corner,
      eraseCornerCellOfNe_eraseCornerCellEmbedding]
  have hspec := succAbove_eraseCornerRelabelValue μ c hc hInsInj d
  change (Fin.cast (eraseCorner_card_add_one μ c hc).symm
      (insertCornerTableau μ c hc T c)).succAbove
        (eraseCornerRelabelValue μ c hc hInsInj d) =
    Fin.cast (eraseCorner_card_add_one μ c hc).symm
      (insertCornerTableau μ c hc T (eraseCornerCellEmbedding μ c hc d)) at hspec
  rw [hpivot, hvalue] at hspec
  simp at hspec
  simpa [eraseCornerRestrictTableau, hInsInj] using hspec

/--
If `c` carries the maximum value in a standard tableau, restricting across
`eraseCorner μ c hc` and then inserting the corner recovers the original
tableau.
-/
theorem insertCorner_eraseCornerRestrict_eq_of_max (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) {T : Cell μ → Fin μ.card}
    (hT : IsStandardTableau μ T) (hcmax : ∀ d : Cell μ, T d ≤ T c) :
    insertCornerTableau μ c hc (eraseCornerRestrictTableau μ c hc hT.1.1) = T := by
  funext d
  have htop := standardTableau_max_value_eq_inserted_top μ c hc hT hcmax
  by_cases hd : d = c
  · subst d
    simp [insertCornerTableau, htop]
  · have hpivot :
      Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c) =
        Fin.last (eraseCorner μ c hc).card := by
      have h := congrArg (Fin.cast (eraseCorner_card_add_one μ c hc).symm) htop
      simpa using h
    have hspec := succAbove_eraseCornerRelabelValue μ c hc hT.1.1
      (eraseCornerCellOfNe μ c hc d hd)
    have hspec_d :
        (Fin.cast (eraseCorner_card_add_one μ c hc).symm (T c)).succAbove
            (eraseCornerRelabelValue μ c hc hT.1.1
              (eraseCornerCellOfNe μ c hc d hd)) =
          Fin.cast (eraseCorner_card_add_one μ c hc).symm (T d) := by
      simpa using hspec
    rw [hpivot] at hspec_d
    simp at hspec_d
    have hcast := congrArg (Fin.cast (eraseCorner_card_add_one μ c hc)) hspec_d
    simpa [insertCornerTableau, eraseCornerRestrictTableau, hd] using hcast

/--
For a fixed corner, standard tableaux of the erased shape are equivalent to
standard tableaux of the original shape whose maximum entry is at that corner.
-/
noncomputable def standardTableauEraseCornerEquiv (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    {T : Cell (eraseCorner μ c hc) → Fin (eraseCorner μ c hc).card //
        IsStandardTableau (eraseCorner μ c hc) T} ≃
      {T : Cell μ → Fin μ.card // IsStandardTableau μ T ∧ IsMaxEntryAt T c} where
  toFun T :=
    ⟨insertCornerTableau μ c hc T.1,
      isStandardTableau_insertCorner μ c hc T.2,
      by
        intro d
        by_cases hd : d = c
        · subst d
          rfl
        · have hle :
            (T.1 (eraseCornerCellOfNe μ c hc d hd)).castSucc ≤
              Fin.last (eraseCorner μ c hc).card :=
            Fin.le_last _
          simpa [insertCornerTableau, hd] using hle⟩
  invFun T :=
    ⟨eraseCornerRestrictTableau μ c hc T.2.1.1.1,
      isStandardTableau_eraseCornerRestrict μ c hc T.2.1⟩
  left_inv T := by
    apply Subtype.ext
    exact eraseCornerRestrict_insertCorner_eq μ c hc T.2
  right_inv T := by
    apply Subtype.ext
    exact insertCorner_eraseCornerRestrict_eq_of_max μ c hc T.2.1 T.2.2

/-- Rewrite the product-shaped maximum-corner tag as a sigma over corner cells. -/
noncomputable def maxCornerStandardTableauxSigmaEquiv (μ : YoungDiagram) :
    MaxCornerStandardTableaux μ ≃ Sigma (FixedMaxStandardTableaux μ) where
  toFun P := ⟨⟨P.1.1, P.2.1⟩, ⟨P.1.2, P.2.2.1, P.2.2.2⟩⟩
  invFun P := ⟨(P.1.1, P.2.1), P.1.2, P.2.2.1, P.2.2.2⟩
  left_inv P := by
    rfl
  right_inv P := by
    rfl

/--
Maximum-corner-tagged tableaux are equivalent to a sigma of erased-shape
standard tableaux over all corner cells.
-/
noncomputable def maxCornerStandardTableauxErasedSigmaEquiv (μ : YoungDiagram) :
    MaxCornerStandardTableaux μ ≃
      Sigma (fun c : CornerCells μ => StandardTableaux (eraseCorner μ c.1 c.2)) :=
  (maxCornerStandardTableauxSigmaEquiv μ).trans <|
    Equiv.sigmaCongrRight fun c => (standardTableauEraseCornerEquiv μ c.1 c.2).symm

/-- A cell with a maximum entry in a standard tableau is a corner cell. -/
theorem isCornerCell_of_tableau_max {μ : YoungDiagram} {T : Cell μ → Fin μ.card}
    (hT : IsStandardTableau μ T) (c : Cell μ) (hcmax : ∀ d : Cell μ, T d ≤ T c) :
    IsCornerCell μ c := by
  intro d hle
  by_contra hdc
  have hlt : T c < T d := hT.2 c d hle (by exact fun h ↦ hdc h.symm)
  exact not_lt_of_ge (hcmax d) hlt

/-- In a nonempty shape, every standard tableau has a maximum-entry corner cell. -/
theorem exists_isCornerCell_of_standardTableau {μ : YoungDiagram} (hμ : μ.cells.Nonempty)
    {T : Cell μ → Fin μ.card} (hT : IsStandardTableau μ T) :
    ∃ c : Cell μ, IsCornerCell μ c ∧ ∀ d : Cell μ, T d ≤ T c := by
  have hatt : μ.cells.attach.Nonempty := by
    rcases hμ with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩, by simp⟩
  obtain ⟨c, _hc, hmax⟩ :=
    Finset.exists_max_image μ.cells.attach (fun c : Cell μ ↦ T c) hatt
  refine ⟨c, isCornerCell_of_tableau_max hT c ?_, ?_⟩
  · intro d
    exact hmax d (by simp)
  · intro d
    exact hmax d (by simp)

/--
Every standard tableau of a nonempty shape has a unique maximum-entry corner,
so all standard tableaux are equivalent to standard tableaux tagged by that
corner.
-/
noncomputable def standardTableauMaxCornerEquiv (μ : YoungDiagram) (hμ : μ.cells.Nonempty) :
    StandardTableaux μ ≃ MaxCornerStandardTableaux μ where
  toFun T :=
    let chosen := Classical.choose (exists_isCornerCell_of_standardTableau hμ T.2)
    let chosen_spec := Classical.choose_spec (exists_isCornerCell_of_standardTableau hμ T.2)
    ⟨(chosen, T.1), chosen_spec.1, T.2, chosen_spec.2⟩
  invFun P := ⟨P.1.2, P.2.2.1⟩
  left_inv T := by
    rfl
  right_inv P := by
    rcases P with ⟨⟨c, T⟩, _hc, hT, hmax⟩
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      apply isMaxEntryAt_unique_of_standard hT
      · exact (Classical.choose_spec (exists_isCornerCell_of_standardTableau hμ hT)).2
      · exact hmax
    · rfl

/--
For a nonempty shape, standard tableaux are equivalent to the sigma of
standard tableaux of all one-corner erasures.
-/
noncomputable def standardTableauxErasedSigmaEquiv (μ : YoungDiagram)
    (hμ : μ.cells.Nonempty) :
    StandardTableaux μ ≃
      Sigma (fun c : CornerCells μ => StandardTableaux (eraseCorner μ c.1 c.2)) :=
  (standardTableauMaxCornerEquiv μ hμ).trans
    (maxCornerStandardTableauxErasedSigmaEquiv μ)

/-- The number of standard tableaux of shape `μ` under the local minimum predicate. -/
noncomputable def standardTableauCount (μ : YoungDiagram) : ℕ := by
  classical
  exact Fintype.card {T : Cell μ → Fin μ.card // IsStandardTableau μ T}

/-- Count standard tableaux by tagging each tableau with its maximum-entry corner. -/
theorem standardTableauCount_eq_maxCornerCard (μ : YoungDiagram) (hμ : μ.cells.Nonempty) :
    standardTableauCount μ = Fintype.card (MaxCornerStandardTableaux μ) := by
  classical
  rw [standardTableauCount]
  exact @Fintype.card_congr (StandardTableaux μ) (MaxCornerStandardTableaux μ)
    (Subtype.fintype (IsStandardTableau μ)) inferInstance
    (standardTableauMaxCornerEquiv μ hμ)

/--
For a nonempty shape, standard tableaux are counted by summing standard
tableaux of all one-corner erasures.
-/
theorem standardTableauCount_eq_sum_erased (μ : YoungDiagram) (hμ : μ.cells.Nonempty) :
    standardTableauCount μ =
      ∑ c : CornerCells μ, standardTableauCount (eraseCorner μ c.1 c.2) := by
  classical
  have hcount (ν : YoungDiagram) :
      standardTableauCount ν = Nat.card (StandardTableaux ν) := by
    rw [standardTableauCount]
    exact (@Nat.card_eq_fintype_card (StandardTableaux ν)
      (Subtype.fintype (IsStandardTableau ν))).symm
  exact calc
    standardTableauCount μ = Nat.card (StandardTableaux μ) := hcount μ
    _ = Nat.card (Sigma (fun c : CornerCells μ =>
          StandardTableaux (eraseCorner μ c.1 c.2))) :=
        Nat.card_congr (standardTableauxErasedSigmaEquiv μ hμ)
    _ = ∑ c : CornerCells μ,
          Nat.card (StandardTableaux (eraseCorner μ c.1 c.2)) :=
        Nat.card_sigma
    _ = ∑ c : CornerCells μ, standardTableauCount (eraseCorner μ c.1 c.2) := by
        simp [standardTableauCount]
    _ = (@Finset.univ (CornerCells μ) inferInstance).sum
          (fun c => standardTableauCount (eraseCorner μ c.1 c.2)) := by
        apply Finset.sum_congr
        · ext c
          simp
        · intro c _hc
          rfl

/-- Product of all hook lengths in the diagram. -/
def hookProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.attach.prod fun c ↦ hookLength μ c

/-- The hook product is positive, including for the empty diagram where the product is one. -/
theorem hookProduct_pos (μ : YoungDiagram) : 0 < hookProduct μ := by
  rw [hookProduct]
  exact Finset.prod_pos fun c _ ↦ hookLength_pos μ c

/-- Split the hook product by deleting the unit hook-length factor at a corner. -/
theorem hookProduct_eq_prod_erase_corner (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    hookProduct μ = (μ.cells.attach.erase c).prod (fun d => hookLength μ d) := by
  rw [hookProduct]
  symm
  exact Finset.prod_erase μ.cells.attach (f := fun d => hookLength μ d)
    (a := c) (hookLength_corner μ c hc)

/-- Rewrite the erased-shape hook product using original hooks with the corner removed. -/
theorem hookProduct_eraseCorner_eq_prod_erased_hooks (μ : YoungDiagram) (c : Cell μ)
    (hc : IsCornerCell μ c) :
    hookProduct (eraseCorner μ c hc) =
      (eraseCorner μ c hc).cells.attach.prod fun d =>
        ((hookCells μ (eraseCornerCellEmbedding μ c hc d)).erase c.val).card := by
  rw [hookProduct]
  apply Finset.prod_congr rfl
  intro d _hd
  rw [hookLength, hookCells_eraseCorner]

/--
Rewrite the erased-shape hook product as a product over the original
non-corner cells.
-/
theorem hookProduct_eraseCorner_eq_prod_noncorner_erased_hooks (μ : YoungDiagram)
    (c : Cell μ) (hc : IsCornerCell μ c) :
    hookProduct (eraseCorner μ c hc) =
      (μ.cells.attach.erase c).prod fun d => ((hookCells μ d).erase c.val).card := by
  rw [hookProduct_eraseCorner_eq_prod_erased_hooks]
  rw [← eraseCornerCellEmbedding_attach_map μ c hc]
  rw [Finset.prod_map]

/--
On original non-corner cells, erasing a corner decrements exactly the hook
factors whose original hook contained that corner.
-/
theorem hookProduct_eraseCorner_eq_prod_noncorner_if (μ : YoungDiagram)
    (c : Cell μ) (hc : IsCornerCell μ c) :
    hookProduct (eraseCorner μ c hc) =
      (μ.cells.attach.erase c).prod fun d =>
        if c.val ∈ hookCells μ d then hookLength μ d - 1 else hookLength μ d := by
  rw [hookProduct_eraseCorner_eq_prod_noncorner_erased_hooks]
  apply Finset.prod_congr rfl
  intro d _hd
  rw [hookLength]
  exact Finset.card_erase_eq_ite

/-- Split the original hook product into affected and unaffected original cells. -/
theorem hookProduct_eq_prod_affected_unaffected (μ : YoungDiagram)
    (c : Cell μ) (hc : IsCornerCell μ c) :
    hookProduct μ =
      (hookAffectedCells μ c).prod (fun d => hookLength μ d) *
        ((μ.cells.attach.erase c).filter fun d => c.val ∉ hookCells μ d).prod
          (fun d => hookLength μ d) := by
  rw [hookProduct_eq_prod_erase_corner μ c hc]
  rw [show (μ.cells.attach.erase c).prod (fun d => hookLength μ d) =
      (μ.cells.attach.erase c).prod
        (fun d => if c.val ∈ hookCells μ d then hookLength μ d else hookLength μ d) by
    apply Finset.prod_congr rfl
    intro d _hd
    by_cases h : c.val ∈ hookCells μ d <;> simp [h]]
  rw [Finset.prod_ite]
  rfl

/-- Split the erased hook product into affected and unaffected original cells. -/
theorem hookProduct_eraseCorner_eq_prod_affected_unaffected (μ : YoungDiagram)
    (c : Cell μ) (hc : IsCornerCell μ c) :
    hookProduct (eraseCorner μ c hc) =
      (hookAffectedCells μ c).prod (fun d => hookLength μ d - 1) *
        ((μ.cells.attach.erase c).filter fun d => c.val ∉ hookCells μ d).prod
          (fun d => hookLength μ d) := by
  rw [hookProduct_eraseCorner_eq_prod_noncorner_if]
  rw [Finset.prod_ite]
  rfl

/-- A hook affected by erasing a distinct corner has positive decremented length. -/
theorem hookLength_sub_one_pos_of_mem_hookAffectedCells
    (μ : YoungDiagram) (c d : Cell μ) (h : d ∈ hookAffectedCells μ c) :
    0 < hookLength μ d - 1 := by
  have hbase : d ∈ μ.cells.attach.erase c := (Finset.mem_filter.mp h).1
  have hcorner : c.val ∈ hookCells μ d := (Finset.mem_filter.mp h).2
  have hdne : d ≠ c := (Finset.mem_erase.mp hbase).1
  have hvalne : d.val ≠ c.val := by
    intro hval
    apply hdne
    exact Subtype.ext hval
  have hdmem : d.val ∈ (hookCells μ d).erase c.val := by
    rw [Finset.mem_erase]
    exact ⟨hvalne, mem_hookCells_self μ d⟩
  have hpos : 0 < ((hookCells μ d).erase c.val).card :=
    Finset.card_pos.mpr ⟨d.val, hdmem⟩
  have hcard : ((hookCells μ d).erase c.val).card = hookLength μ d - 1 := by
    rw [hookLength]
    exact Finset.card_erase_of_mem hcorner
  rwa [hcard] at hpos

/-- The original-to-erased hook-product ratio depends only on affected hook factors. -/
theorem hookProduct_div_eraseCorner_eq_affected_div
    (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (hookProduct μ : ℚ) / hookProduct (eraseCorner μ c hc) =
      (((hookAffectedCells μ c).prod (fun d => hookLength μ d) : ℕ) : ℚ) /
        (((hookAffectedCells μ c).prod (fun d => hookLength μ d - 1) : ℕ) : ℚ) := by
  let A : ℕ := (hookAffectedCells μ c).prod (fun d => hookLength μ d)
  let B : ℕ := (hookAffectedCells μ c).prod (fun d => hookLength μ d - 1)
  let U : ℕ :=
    ((μ.cells.attach.erase c).filter fun d => c.val ∉ hookCells μ d).prod
      (fun d => hookLength μ d)
  have hBpos : 0 < B := by
    dsimp [B]
    apply Finset.prod_pos
    intro d hd
    exact hookLength_sub_one_pos_of_mem_hookAffectedCells μ c d hd
  have hUpos : 0 < U := by
    dsimp [U]
    apply Finset.prod_pos
    intro d _hd
    exact hookLength_pos μ d
  have hB : (B : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hBpos)
  have hU : (U : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hUpos)
  rw [hookProduct_eq_prod_affected_unaffected μ c hc]
  rw [hookProduct_eraseCorner_eq_prod_affected_unaffected μ c hc]
  change ((A * U : ℕ) : ℚ) / ((B * U : ℕ) : ℚ) = (A : ℚ) / (B : ℚ)
  field_simp [hB, hU]
  norm_num [Nat.cast_mul]
  ring

/--
The original-to-erased hook-product ratio as explicit row and column interval
products.
-/
theorem hookProduct_div_eraseCorner_eq_interval_products
    (μ : YoungDiagram) (c : Cell μ) (hc : IsCornerCell μ c) :
    (hookProduct μ : ℚ) / hookProduct (eraseCorner μ c hc) =
      (((Finset.Ico 0 c.val.2).prod
          (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1)) *
        (Finset.Ico 0 c.val.1).prod
          (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i)) : ℕ) : ℚ) /
      (((Finset.Ico 0 c.val.2).prod
          (fun j => (c.val.2 - j) + (μ.colLen j - c.val.1) - 1) *
        (Finset.Ico 0 c.val.1).prod
          (fun i => (μ.rowLen i - c.val.2) + (c.val.1 - i) - 1) : ℕ) : ℚ) := by
  rw [hookProduct_div_eraseCorner_eq_affected_div]
  rw [hookAffectedCells_prod_hookLength_eq_interval_products μ c hc]
  rw [hookAffectedCells_prod_hookLength_sub_one_eq_interval_products μ c hc]

/-- The corner summand in the hook-product branching identity. -/
noncomputable def hookProductCornerRatio (μ : YoungDiagram) (c : CornerCells μ) : ℚ :=
  (hookProduct μ : ℚ) / hookProduct (eraseCorner μ c.1 c.2)

/-- The same corner summand, expanded as row and column interval products. -/
noncomputable def hookProductCornerIntervalRatio (μ : YoungDiagram) (c : CornerCells μ) : ℚ :=
  let rowNum : ℕ := (Finset.Ico 0 c.1.val.2).prod
    (fun j => (c.1.val.2 - j) + (μ.colLen j - c.1.val.1))
  let colNum : ℕ := (Finset.Ico 0 c.1.val.1).prod
    (fun i => (μ.rowLen i - c.1.val.2) + (c.1.val.1 - i))
  let rowDen : ℕ := (Finset.Ico 0 c.1.val.2).prod
    (fun j => (c.1.val.2 - j) + (μ.colLen j - c.1.val.1) - 1)
  let colDen : ℕ := (Finset.Ico 0 c.1.val.1).prod
    (fun i => (μ.rowLen i - c.1.val.2) + (c.1.val.1 - i) - 1)
  ((rowNum * colNum : ℕ) : ℚ) / ((rowDen * colDen : ℕ) : ℚ)

/-- Column coordinate of the corner associated to a row drop. -/
def rowDropCornerCol (μ : YoungDiagram) (r : CornerRows μ) : ℕ :=
  μ.rowLen r.1 - 1

/-- Numerator of the row-drop-indexed interval-product hook summand. -/
def hookProductRowDropIntervalNumerator (μ : YoungDiagram) (r : CornerRows μ) : ℕ :=
  let cornerCol : ℕ := rowDropCornerCol μ r
  let rowNum : ℕ := (Finset.Ico 0 cornerCol).prod
    (fun j => (cornerCol - j) + (μ.colLen j - r.1))
  let colNum : ℕ := (Finset.Ico 0 r.1).prod
    (fun i => (μ.rowLen i - cornerCol) + (r.1 - i))
  rowNum * colNum

/-- Denominator of the row-drop-indexed interval-product hook summand. -/
def hookProductRowDropIntervalDenominator (μ : YoungDiagram) (r : CornerRows μ) : ℕ :=
  let cornerCol : ℕ := rowDropCornerCol μ r
  let rowDen : ℕ := (Finset.Ico 0 cornerCol).prod
    (fun j => (cornerCol - j) + (μ.colLen j - r.1) - 1)
  let colDen : ℕ := (Finset.Ico 0 r.1).prod
    (fun i => (μ.rowLen i - cornerCol) + (r.1 - i) - 1)
  rowDen * colDen

/-- Row-drop-indexed interval-product form of a corner hook-product summand. -/
noncomputable def hookProductRowDropIntervalRatio (μ : YoungDiagram) (r : CornerRows μ) : ℚ :=
  (hookProductRowDropIntervalNumerator μ r : ℚ) /
    hookProductRowDropIntervalDenominator μ r

/-- Hook-product branching identity needed by the induction route. -/
def HookProductBranchingIdentity : Prop :=
  ∀ μ : YoungDiagram, μ.cells.Nonempty →
    (Finset.univ.sum fun c : CornerCells μ => hookProductCornerRatio μ c) = (μ.card : ℚ)

/-- Row-drop-indexed form of the hook-product branching identity. -/
def HookProductBranchingRowDropIdentity : Prop :=
  ∀ μ : YoungDiagram, μ.cells.Nonempty →
    (Finset.univ.sum fun r : CornerRows μ =>
      hookProductCornerRatio μ (cornerRowsEquivCornerCells μ r)) = (μ.card : ℚ)

/-- Explicit interval-product form of the row-drop branching identity. -/
def HookProductBranchingRowDropIntervalIdentity : Prop :=
  ∀ μ : YoungDiagram, μ.cells.Nonempty →
    (Finset.univ.sum fun r : CornerRows μ => hookProductRowDropIntervalRatio μ r) =
      (μ.card : ℚ)

/-- Interval-product form of the hook-product branching identity. -/
def HookProductBranchingIntervalIdentity : Prop :=
  ∀ μ : YoungDiagram, μ.cells.Nonempty →
    (Finset.univ.sum fun c : CornerCells μ => hookProductCornerIntervalRatio μ c) =
      (μ.card : ℚ)

/-- The corner hook-product ratio agrees with its interval-product expansion. -/
theorem hookProductCornerRatio_eq_interval (μ : YoungDiagram) (c : CornerCells μ) :
    hookProductCornerRatio μ c = hookProductCornerIntervalRatio μ c := by
  rw [hookProductCornerRatio, hookProductCornerIntervalRatio]
  exact hookProduct_div_eraseCorner_eq_interval_products μ c.1 c.2

/-- A transported corner summand is the row-drop interval-product ratio. -/
theorem hookProductCornerRatio_eq_rowDropInterval (μ : YoungDiagram) (r : CornerRows μ) :
    hookProductCornerRatio μ (cornerRowsEquivCornerCells μ r) =
      hookProductRowDropIntervalRatio μ r := by
  rw [hookProductCornerRatio_eq_interval]
  rfl

/-- The row-drop corner column is inside the row that drops. -/
theorem rowDropCornerCol_lt_rowLen (μ : YoungDiagram) (r : CornerRows μ) :
    rowDropCornerCol μ r < μ.rowLen r.1 := by
  have hdrop : μ.rowLen (r.1 + 1) < μ.rowLen r.1 := (Finset.mem_filter.mp r.2).2
  dsimp [rowDropCornerCol]
  omega

/-- Row part denominator factors in the row-drop interval ratio are positive. -/
theorem rowDropInterval_rowDenFactor_pos (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    0 < (rowDropCornerCol μ r - j) + (μ.colLen j - r.1) - 1 := by
  have hjlt : j < rowDropCornerCol μ r := (Finset.mem_Ico.mp hj).2
  have hjrow : j < μ.rowLen r.1 := by
    have hcorner := rowDropCornerCol_lt_rowLen μ r
    omega
  have hcell : (r.1, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hjrow
  have hcollt : r.1 < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hcell
  omega

/-- Column part denominator factors in the row-drop interval ratio are positive. -/
theorem rowDropInterval_colDenFactor_pos (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i ∈ Finset.Ico 0 r.1) :
    0 < (μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) - 1 := by
  have hilt : i < r.1 := (Finset.mem_Ico.mp hi).2
  have hcorner_col_lt : rowDropCornerCol μ r < μ.rowLen r.1 :=
    rowDropCornerCol_lt_rowLen μ r
  have hcorner_mem : (r.1, rowDropCornerCol μ r) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr hcorner_col_lt
  have hi_mem : (i, rowDropCornerCol μ r) ∈ μ :=
    μ.up_left_mem (Nat.le_of_lt hilt) le_rfl hcorner_mem
  have hirow : rowDropCornerCol μ r < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_rowLen.mp hi_mem
  omega

/-- The explicit row-drop interval denominator is positive. -/
theorem hookProductRowDropIntervalDenominator_pos (μ : YoungDiagram) (r : CornerRows μ) :
    0 < hookProductRowDropIntervalDenominator μ r := by
  dsimp [hookProductRowDropIntervalDenominator, rowDropCornerCol]
  apply Nat.mul_pos
  · exact Finset.prod_pos (fun j hj => rowDropInterval_rowDenFactor_pos μ r hj)
  · exact Finset.prod_pos (fun i hi => rowDropInterval_colDenFactor_pos μ r hi)

/-- The explicit row-drop interval denominator is nonzero as a rational. -/
theorem hookProductRowDropIntervalDenominator_ne_zero (μ : YoungDiagram) (r : CornerRows μ) :
    (hookProductRowDropIntervalDenominator μ r : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (hookProductRowDropIntervalDenominator_pos μ r))

/-- Row part numerator factors in the row-drop interval ratio are positive. -/
theorem rowDropInterval_rowNumFactor_pos (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    0 < (rowDropCornerCol μ r - j) + (μ.colLen j - r.1) := by
  have h := rowDropInterval_rowDenFactor_pos μ r hj
  omega

/-- Column part numerator factors in the row-drop interval ratio are positive. -/
theorem rowDropInterval_colNumFactor_pos (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i ∈ Finset.Ico 0 r.1) :
    0 < (μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) := by
  have h := rowDropInterval_colDenFactor_pos μ r hi
  omega

/-- The explicit row-drop interval numerator is positive. -/
theorem hookProductRowDropIntervalNumerator_pos (μ : YoungDiagram) (r : CornerRows μ) :
    0 < hookProductRowDropIntervalNumerator μ r := by
  dsimp [hookProductRowDropIntervalNumerator]
  apply Nat.mul_pos
  · exact Finset.prod_pos (fun j hj => rowDropInterval_rowNumFactor_pos μ r hj)
  · exact Finset.prod_pos (fun i hi => rowDropInterval_colNumFactor_pos μ r hi)

/-- The explicit row-drop interval hook-product summand is positive. -/
theorem hookProductRowDropIntervalRatio_pos (μ : YoungDiagram) (r : CornerRows μ) :
    0 < hookProductRowDropIntervalRatio μ r := by
  rw [hookProductRowDropIntervalRatio]
  apply div_pos
  · exact_mod_cast hookProductRowDropIntervalNumerator_pos μ r
  · exact_mod_cast hookProductRowDropIntervalDenominator_pos μ r

/-- Integer content of the row-drop corner. -/
def rowDropContent (μ : YoungDiagram) (r : CornerRows μ) : ℤ :=
  (rowDropCornerCol μ r : ℤ) - (r.1 : ℤ)

/-- Integer content boundary associated to a column height. -/
def colBoundaryContent (μ : YoungDiagram) (j : ℕ) : ℤ :=
  (j : ℤ) - (μ.colLen j : ℤ)

/-- Integer content boundary associated to a row length. -/
def rowBoundaryContent (μ : YoungDiagram) (i : ℕ) : ℤ :=
  (μ.rowLen i : ℤ) - (i : ℤ)

/-- Row boundary contents strictly decrease as row indices increase. -/
theorem rowBoundaryContent_strictAnti (μ : YoungDiagram) {i k : ℕ} (h : i < k) :
    rowBoundaryContent μ k < rowBoundaryContent μ i := by
  have hrow : μ.rowLen k ≤ μ.rowLen i := μ.rowLen_anti i k (Nat.le_of_lt h)
  dsimp [rowBoundaryContent]
  omega

/-- Column boundary contents strictly increase as column indices increase. -/
theorem colBoundaryContent_strictMono (μ : YoungDiagram) {j k : ℕ} (h : j < k) :
    colBoundaryContent μ j < colBoundaryContent μ k := by
  have hcol : μ.colLen k ≤ μ.colLen j := μ.colLen_anti j k (Nat.le_of_lt h)
  dsimp [colBoundaryContent]
  omega

/-- If row lengths do not strictly drop, the next row has the same length. -/
theorem rowLen_succ_eq_of_not_drop (μ : YoungDiagram) {i : ℕ}
    (hnot : ¬ μ.rowLen (i + 1) < μ.rowLen i) :
    μ.rowLen (i + 1) = μ.rowLen i := by
  have hle : μ.rowLen (i + 1) ≤ μ.rowLen i := μ.rowLen_anti i (i + 1) (Nat.le_succ i)
  omega

/-- Across a non-drop row step, row boundary content decreases by one. -/
theorem rowBoundaryContent_succ_eq_sub_one_of_not_drop (μ : YoungDiagram) {i : ℕ}
    (hnot : ¬ μ.rowLen (i + 1) < μ.rowLen i) :
    rowBoundaryContent μ (i + 1) = rowBoundaryContent μ i - 1 := by
  have hrow := rowLen_succ_eq_of_not_drop μ hnot
  dsimp [rowBoundaryContent]
  omega

/-- Across a strict row drop, row boundary content decreases by more than one. -/
theorem rowBoundaryContent_succ_lt_sub_one_of_drop (μ : YoungDiagram) {i : ℕ}
    (hdrop : μ.rowLen (i + 1) < μ.rowLen i) :
    rowBoundaryContent μ (i + 1) < rowBoundaryContent μ i - 1 := by
  dsimp [rowBoundaryContent]
  omega

/-- Before a fixed removable row, a non-corner row step shifts boundary content by one. -/
theorem rowBoundaryContent_succ_eq_sub_one_of_not_mem_cornerRow
    (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i < r.1) (hnot : i ∉ cornerRowIndices μ) :
    rowBoundaryContent μ (i + 1) = rowBoundaryContent μ i - 1 := by
  apply rowBoundaryContent_succ_eq_sub_one_of_not_drop
  intro hdrop
  exact hnot ((mem_cornerRowIndices_iff_of_lt_cornerRow μ r hi).mpr hdrop)

/-- On a non-corner row step, the shifted denominator factor is the next numerator factor. -/
theorem rowBoundaryContent_den_eq_succ_num_of_not_mem_cornerRow
    (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i < r.1) (hnot : i ∉ cornerRowIndices μ) :
    rowBoundaryContent μ i - rowDropContent μ r - 1 =
      rowBoundaryContent μ (i + 1) - rowDropContent μ r := by
  rw [rowBoundaryContent_succ_eq_sub_one_of_not_mem_cornerRow μ r hi hnot]
  ring

/-- If column heights do not strictly drop, the next column has the same height. -/
theorem colLen_succ_eq_of_not_drop (μ : YoungDiagram) {j : ℕ}
    (hnot : ¬ μ.colLen (j + 1) < μ.colLen j) :
    μ.colLen (j + 1) = μ.colLen j := by
  have hle : μ.colLen (j + 1) ≤ μ.colLen j := μ.colLen_anti j (j + 1) (Nat.le_succ j)
  omega

/-- Across a non-drop column step, column boundary content increases by one. -/
theorem colBoundaryContent_succ_eq_add_one_of_not_drop (μ : YoungDiagram) {j : ℕ}
    (hnot : ¬ μ.colLen (j + 1) < μ.colLen j) :
    colBoundaryContent μ (j + 1) = colBoundaryContent μ j + 1 := by
  have hcol := colLen_succ_eq_of_not_drop μ hnot
  dsimp [colBoundaryContent]
  omega

/-- Across a strict column drop, column boundary content increases by more than one. -/
theorem colBoundaryContent_add_one_lt_succ_of_drop (μ : YoungDiagram) {j : ℕ}
    (hdrop : μ.colLen (j + 1) < μ.colLen j) :
    colBoundaryContent μ j + 1 < colBoundaryContent μ (j + 1) := by
  dsimp [colBoundaryContent]
  omega

/-- Row boundary content is injective as a function of the row index. -/
theorem rowBoundaryContent_injective (μ : YoungDiagram) :
    Function.Injective (rowBoundaryContent μ) := by
  intro i k h
  rcases lt_trichotomy i k with hlt | heq | hgt
  · have hstrict := rowBoundaryContent_strictAnti μ hlt
    omega
  · exact heq
  · have hstrict := rowBoundaryContent_strictAnti μ hgt
    omega

/-- Column boundary content is injective as a function of the column index. -/
theorem colBoundaryContent_injective (μ : YoungDiagram) :
    Function.Injective (colBoundaryContent μ) := by
  intro j k h
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have hstrict := colBoundaryContent_strictMono μ hlt
    omega
  · exact heq
  · have hstrict := colBoundaryContent_strictMono μ hgt
    omega

/-- A row-drop corner content is the row boundary content one step below. -/
theorem rowDropContent_eq_rowBoundaryContent_sub_one (μ : YoungDiagram) (r : CornerRows μ) :
    rowDropContent μ r = rowBoundaryContent μ r.1 - 1 := by
  have hpos : 0 < μ.rowLen r.1 := by
    have hcorner := rowDropCornerCol_lt_rowLen μ r
    omega
  dsimp [rowDropContent, rowBoundaryContent, rowDropCornerCol]
  omega

/-- The current removable row boundary is one above its row-drop content. -/
theorem rowBoundaryContent_sub_rowDropContent_self (μ : YoungDiagram) (r : CornerRows μ) :
    rowBoundaryContent μ r.1 - rowDropContent μ r = 1 := by
  rw [rowDropContent_eq_rowBoundaryContent_sub_one]
  ring

/-- The current row-drop content is one below its row boundary. -/
theorem rowDropContent_sub_rowBoundaryContent_self (μ : YoungDiagram) (r : CornerRows μ) :
    rowDropContent μ r - rowBoundaryContent μ r.1 = -1 := by
  rw [rowDropContent_eq_rowBoundaryContent_sub_one]
  ring

/--
Row boundary contents above a fixed removable row telescope, leaving only the
strict row-drop boundary factors.
-/
theorem rowBoundaryContent_prod_telescope_before_corner
    (μ : YoungDiagram) (r : CornerRows μ) :
    ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))) *
        (((cornerRowIndices μ).filter fun s => s < r.1).prod
          (fun s => ((rowBoundaryContent μ s - rowDropContent μ r - 1 : ℤ) : ℚ))) =
      ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))) *
        (((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ) *
          (((cornerRowIndices μ).filter fun s => s < r.1).prod
            (fun s => ((rowBoundaryContent μ (s + 1) - rowDropContent μ r : ℤ) : ℚ)))) := by
  have htel := prod_Ico_telescope_with_drops (cornerRowIndices μ) (M := ℚ)
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))
    r.1 ?_
  · have hself : (((rowBoundaryContent μ r.1 - rowDropContent μ r : ℤ) : ℚ)) = 1 := by
      exact_mod_cast rowBoundaryContent_sub_rowDropContent_self μ r
    rw [hself, one_mul] at htel
    simpa [mul_assoc] using htel
  · intro i hi hnot
    exact_mod_cast rowBoundaryContent_den_eq_succ_num_of_not_mem_cornerRow μ r hi hnot

/--
Row boundary contents above a fixed removable row telescope in the orientation
used by the addable/removable content ratio.
-/
theorem rowBoundaryContent_prod_telescope_before_corner_content
    (μ : YoungDiagram) (r : CornerRows μ) :
    ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))) *
        (((cornerRowIndices μ).filter fun s => s < r.1).prod
          (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) =
      ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))) *
        (((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ) *
          (((cornerRowIndices μ).filter fun s => s < r.1).prod
            (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ)))) := by
  let S := (cornerRowIndices μ).filter fun s => s < r.1
  let RN := (Finset.Ico 0 r.1).prod
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))
  let RD := (Finset.Ico 0 r.1).prod
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))
  let DA := S.prod (fun s => ((rowBoundaryContent μ s - rowDropContent μ r - 1 : ℤ) : ℚ))
  let SA := S.prod (fun s => ((rowBoundaryContent μ (s + 1) - rowDropContent μ r : ℤ) : ℚ))
  let DAc := S.prod (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))
  let SAc := S.prod (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ))
  have htel : RN * DA = RD * (((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ) * SA) := by
    simpa [S, RN, RD, DA, SA] using rowBoundaryContent_prod_telescope_before_corner μ r
  have hDAc : DAc = (-1 : ℚ) ^ S.card * DA := by
    dsimp [DAc, DA]
    rw [show (S.prod fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ)) =
        S.prod (fun s => -(((rowBoundaryContent μ s - rowDropContent μ r - 1 : ℤ) : ℚ))) by
      apply Finset.prod_congr rfl
      intro s _hs
      exact_mod_cast (show rowDropContent μ r - (rowBoundaryContent μ s - 1) =
        -(rowBoundaryContent μ s - rowDropContent μ r - 1) by ring)]
    rw [Finset.prod_neg]
  have hSAc : SAc = (-1 : ℚ) ^ S.card * SA := by
    dsimp [SAc, SA]
    rw [show (S.prod fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ)) =
        S.prod (fun s => -(((rowBoundaryContent μ (s + 1) - rowDropContent μ r : ℤ) : ℚ))) by
      apply Finset.prod_congr rfl
      intro s _hs
      exact_mod_cast (show rowDropContent μ r - rowBoundaryContent μ (s + 1) =
        -(rowBoundaryContent μ (s + 1) - rowDropContent μ r) by ring)]
    rw [Finset.prod_neg]
  dsimp [S, RN, RD, DAc, SAc] at hDAc hSAc ⊢
  rw [hDAc, hSAc]
  calc
    RN * (((-1 : ℚ) ^ S.card) * DA) = ((-1 : ℚ) ^ S.card) * (RN * DA) := by ring
    _ = ((-1 : ℚ) ^ S.card) *
        (RD * (((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ) * SA)) := by
          rw [htel]
    _ = RD * (((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ) *
        (((-1 : ℚ) ^ S.card) * SA)) := by ring

/-- Column indices before a row-drop corner where the column height strictly drops. -/
def colDropIndicesBeforeRowDrop (μ : YoungDiagram) (r : CornerRows μ) : Finset ℕ :=
  (Finset.range (rowDropCornerCol μ r)).filter fun j => μ.colLen (j + 1) < μ.colLen j

/-- Column boundary indices contributing addable-row factors below a fixed row drop. -/
def colAddableBoundaryIndicesBeforeRowDrop (μ : YoungDiagram) (r : CornerRows μ) : Finset ℕ :=
  insert 0 ((colDropIndicesBeforeRowDrop μ r).image fun j => j + 1)

/-- Products over the column addable-boundary indices split into the bottom and drop successors. -/
theorem colAddableBoundaryIndicesBeforeRowDrop_prod_eq_zero_mul_succ
    (μ : YoungDiagram) (r : CornerRows μ) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (colAddableBoundaryIndicesBeforeRowDrop μ r).prod f =
      f 0 * (colDropIndicesBeforeRowDrop μ r).prod (fun j => f (j + 1)) := by
  have hnot : 0 ∉ (colDropIndicesBeforeRowDrop μ r).image (fun j => j + 1) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨j, _hj, hsucc⟩
    omega
  have hinj : Set.InjOn (fun j : ℕ => j + 1) (colDropIndicesBeforeRowDrop μ r) := by
    intro a _ha b _hb h
    change a + 1 = b + 1 at h
    omega
  rw [colAddableBoundaryIndicesBeforeRowDrop, Finset.prod_insert hnot, Finset.prod_image hinj]

/-- The first row below all nonempty rows has row length zero. -/
theorem rowLen_colLen_zero_eq_zero (μ : YoungDiagram) :
    μ.rowLen (μ.colLen 0) = 0 := by
  by_contra hnot
  have hpos : 0 < μ.rowLen (μ.colLen 0) := by omega
  have hcell : (μ.colLen 0, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
  have hlt : μ.colLen 0 < μ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hcell
  omega

/-- The bottom addable row boundary has the same content as the zero column boundary. -/
theorem rowBoundaryContent_colLen_zero_eq_colBoundaryContent_zero (μ : YoungDiagram) :
    rowBoundaryContent μ (μ.colLen 0) = colBoundaryContent μ 0 := by
  have hrow := rowLen_colLen_zero_eq_zero μ
  dsimp [rowBoundaryContent, colBoundaryContent]
  rw [hrow]
  omega

/-- Addable row-boundary contents and removable row-drop contents have equal sums. -/
theorem addableRowIndices_sum_rowBoundaryContent_eq_cornerRowIndices_sum_rowDropContent
    (μ : YoungDiagram) :
    (addableRowIndices μ).sum (fun a => rowBoundaryContent μ a) =
      (cornerRowIndices μ).sum (fun r => rowBoundaryContent μ r - 1) := by
  let n := μ.colLen 0
  let N : ℕ → ℤ := fun i => rowBoundaryContent μ i
  let D : ℕ → ℤ := fun i => rowBoundaryContent μ i - 1
  have htel := sum_Ico_telescope_with_drops (cornerRowIndices μ) N D n ?_
  · have hfilter : (cornerRowIndices μ).filter (fun i => i < n) = cornerRowIndices μ := by
      dsimp [n]
      exact cornerRowIndices_filter_lt_colLen_zero μ
    have hbottom : N n = - (n : ℤ) := by
      dsimp [N, n, rowBoundaryContent]
      rw [rowLen_colLen_zero_eq_zero]
      omega
    have hsumD : (Finset.Ico 0 n).sum D = (Finset.Ico 0 n).sum N - (n : ℤ) := by
      dsimp [D, N]
      rw [Finset.sum_sub_distrib]
      simp
    rw [hfilter] at htel
    have hadd := addableRowIndices_sum_eq_zero_add_succ μ
      (fun a => rowBoundaryContent μ a)
    dsimp [N, D] at htel hbottom hsumD hadd ⊢
    rw [hadd]
    linarith
  · intro i hi hnot
    dsimp [N, D]
    have hnotdrop : ¬ μ.rowLen (i + 1) < μ.rowLen i := by
      intro hdrop
      apply hnot
      rw [cornerRowIndices, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hi, hdrop⟩
    rw [rowBoundaryContent_succ_eq_sub_one_of_not_drop μ hnotdrop]

/--
The addable/removable row-boundary square difference is twice the number of
cells.
-/
theorem addableRowIndices_sum_sq_rowBoundaryContent_sub_cornerRowIndices_sum_sq_eq_card
    (μ : YoungDiagram) :
    (addableRowIndices μ).sum (fun a => (rowBoundaryContent μ a) ^ 2) -
      (cornerRowIndices μ).sum (fun r => (rowBoundaryContent μ r - 1) ^ 2) =
        (2 : ℤ) * (μ.card : ℤ) := by
  let n := μ.colLen 0
  let N : ℕ → ℤ := fun i => (rowBoundaryContent μ i) ^ 2
  let D : ℕ → ℤ := fun i => (rowBoundaryContent μ i - 1) ^ 2
  have htel := sum_Ico_telescope_with_drops (cornerRowIndices μ) N D n ?_
  · have hfilter : (cornerRowIndices μ).filter (fun i => i < n) = cornerRowIndices μ := by
      dsimp [n]
      exact cornerRowIndices_filter_lt_colLen_zero μ
    rw [hfilter] at htel
    have hbottom : N n = (n : ℤ) ^ 2 := by
      dsimp [N, n, rowBoundaryContent]
      rw [rowLen_colLen_zero_eq_zero]
      ring
    have hsumDiff : (Finset.Ico 0 n).sum N - (Finset.Ico 0 n).sum D + N n =
        (2 : ℤ) * (μ.card : ℤ) := by
      have hdiff : (Finset.Ico 0 n).sum N - (Finset.Ico 0 n).sum D =
          (Finset.Ico 0 n).sum (fun i => (2 : ℤ) * rowBoundaryContent μ i - 1) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      rw [hdiff, hbottom]
      have hodd : ((Finset.range n).sum (fun i => ((2 * i + 1 : ℕ) : ℤ))) =
          (n : ℤ) ^ 2 := by
        exact_mod_cast sum_range_odd n
      have hrowCard : (μ.card : ℤ) =
          ((Finset.range n).sum (fun i => (μ.rowLen i : ℕ)) : ℤ) := by
        dsimp [n]
        exact_mod_cast card_eq_sum_rowLen μ
      rw [hrowCard]
      simp only [← Finset.range_eq_Ico]
      calc
        (Finset.range n).sum (fun i => (2 : ℤ) * rowBoundaryContent μ i - 1) +
              (n : ℤ) ^ 2 =
            (Finset.range n).sum
                (fun i => (2 : ℤ) * (μ.rowLen i : ℤ) - ((2 * i + 1 : ℕ) : ℤ)) +
              (n : ℤ) ^ 2 := by
          congr 2
          funext i
          dsimp [rowBoundaryContent]
          ring
        _ = (2 : ℤ) * (Finset.range n).sum (fun i => (μ.rowLen i : ℤ)) -
              (Finset.range n).sum (fun i => ((2 * i + 1 : ℕ) : ℤ)) +
            (n : ℤ) ^ 2 := by
          rw [Finset.sum_sub_distrib]
          rw [show (Finset.range n).sum (fun i => (2 : ℤ) * (μ.rowLen i : ℤ)) =
              (2 : ℤ) * (Finset.range n).sum (fun i => (μ.rowLen i : ℤ)) by
            rw [← Finset.mul_sum]]
        _ = (2 : ℤ) * (Finset.range n).sum (fun i => (μ.rowLen i : ℤ)) := by
          rw [hodd]
          ring
    have hadd := addableRowIndices_sum_eq_zero_add_succ μ
      (fun a => (rowBoundaryContent μ a) ^ 2)
    dsimp [N, D] at htel hsumDiff hadd ⊢
    rw [hadd]
    linarith
  · intro i hi hnot
    dsimp [N, D]
    have hnotdrop : ¬ μ.rowLen (i + 1) < μ.rowLen i := by
      intro hdrop
      apply hnot
      rw [cornerRowIndices, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hi, hdrop⟩
    rw [rowBoundaryContent_succ_eq_sub_one_of_not_drop μ hnotdrop]

/-- The bottom nonempty row is a removable row whenever a removable row exists. -/
theorem lastCornerRow_mem_cornerRowIndices (μ : YoungDiagram) (r : CornerRows μ) :
    μ.colLen 0 - 1 ∈ cornerRowIndices μ := by
  have hrange : r.1 ∈ Finset.range (μ.colLen 0) := (Finset.mem_filter.mp r.2).1
  have hrlt : r.1 < μ.colLen 0 := Finset.mem_range.mp hrange
  have hcolpos : 0 < μ.colLen 0 := by omega
  rw [cornerRowIndices, Finset.mem_filter]
  constructor
  · exact Finset.mem_range.mpr (by omega)
  · have hrow_last_pos : 0 < μ.rowLen (μ.colLen 0 - 1) := by
      have hlt : μ.colLen 0 - 1 < μ.colLen 0 := by omega
      have hcell : (μ.colLen 0 - 1, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hrow_after := rowLen_colLen_zero_eq_zero μ
    have hsucc : μ.colLen 0 - 1 + 1 = μ.colLen 0 := by omega
    rw [hsucc]
    omega

/-- The column at the addable boundary below a removable row has height one past that row. -/
theorem colLen_rowLen_succ_eq_succ_of_cornerRow
    (μ : YoungDiagram) {s : ℕ} (hs : s ∈ cornerRowIndices μ) :
    μ.colLen (μ.rowLen (s + 1)) = s + 1 := by
  have hdrop : μ.rowLen (s + 1) < μ.rowLen s := (Finset.mem_filter.mp hs).2
  have hcell_s : (s, μ.rowLen (s + 1)) ∈ μ := by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    exact hdrop
  have hs_lt_col : s < μ.colLen (μ.rowLen (s + 1)) :=
    YoungDiagram.mem_iff_lt_colLen.mp hcell_s
  have hnot_cell_next : ¬ (s + 1, μ.rowLen (s + 1)) ∈ μ := by
    intro hcell
    have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    omega
  have hcol_le : μ.colLen (μ.rowLen (s + 1)) ≤ s + 1 := by
    by_contra hnot
    have hgt : s + 1 < μ.colLen (μ.rowLen (s + 1)) := by omega
    exact hnot_cell_next (YoungDiagram.mem_iff_lt_colLen.mpr hgt)
  omega

/-- A successor row boundary at a removable row is the matching column boundary. -/
theorem rowBoundaryContent_succ_eq_colBoundaryContent_rowLen_succ_of_cornerRow
    (μ : YoungDiagram) {s : ℕ} (hs : s ∈ cornerRowIndices μ) :
    rowBoundaryContent μ (s + 1) = colBoundaryContent μ (μ.rowLen (s + 1)) := by
  have hcol := colLen_rowLen_succ_eq_succ_of_cornerRow μ hs
  dsimp [rowBoundaryContent, colBoundaryContent]
  rw [hcol]
  omega

/-- A strict column drop before a fixed removable row identifies a corner row at its top. -/
theorem colDropTopCornerRow_mem_cornerRowIndices_ge
    (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ colDropIndicesBeforeRowDrop μ r) :
    μ.colLen (j + 1) - 1 ∈ (cornerRowIndices μ).filter fun s => r.1 ≤ s := by
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter] at hj
  rcases hj with ⟨hjrange, hjdrop⟩
  have hjlt : j < rowDropCornerCol μ r := Finset.mem_range.mp hjrange
  have hcorner := rowDropCornerCol_lt_rowLen μ r
  have hjlt_row : j < μ.rowLen r.1 - 1 := by
    simpa [rowDropCornerCol] using hjlt
  have hcorner_row : μ.rowLen r.1 - 1 < μ.rowLen r.1 := by
    simpa [rowDropCornerCol] using hcorner
  have hr_cell : (r.1, j + 1) ∈ μ := by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    omega
  have hr_lt_colsucc : r.1 < μ.colLen (j + 1) :=
    YoungDiagram.mem_iff_lt_colLen.mp hr_cell
  have hcolsucc_pos : 0 < μ.colLen (j + 1) := by omega
  let s := μ.colLen (j + 1) - 1
  have hs_lt_colsucc : s < μ.colLen (j + 1) := by
    dsimp [s]
    omega
  have hs_cell_succ : (s, j + 1) ∈ μ :=
    YoungDiagram.mem_iff_lt_colLen.mpr hs_lt_colsucc
  have hrow_gt_succ : j + 1 < μ.rowLen s :=
    YoungDiagram.mem_iff_lt_rowLen.mp hs_cell_succ
  have hnot_cell_next_succ : ¬ (s + 1, j + 1) ∈ μ := by
    intro hcell
    have hslt := YoungDiagram.mem_iff_lt_colLen.mp hcell
    dsimp [s] at hslt
    omega
  have hrow_next_le : μ.rowLen (s + 1) ≤ j + 1 := by
    by_contra hnot
    have hgt : j + 1 < μ.rowLen (s + 1) := by omega
    exact hnot_cell_next_succ (YoungDiagram.mem_iff_lt_rowLen.mpr hgt)
  have hrowdrop : μ.rowLen (s + 1) < μ.rowLen s := by omega
  have hr_le_s : r.1 ≤ s := by
    dsimp [s]
    omega
  rw [Finset.mem_filter]
  constructor
  · rw [cornerRowIndices, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hcolle : μ.colLen (j + 1) ≤ μ.colLen 0 :=
        μ.colLen_anti 0 (j + 1) (Nat.zero_le _)
      omega
    · simpa [s] using hrowdrop
  · simpa [s] using hr_le_s

/-- At a strict column drop, the first row below the upper block has length `j + 1`. -/
theorem rowLen_colLen_succ_eq_succ_of_colDrop
    (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ colDropIndicesBeforeRowDrop μ r) :
    μ.rowLen (μ.colLen (j + 1)) = j + 1 := by
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter] at hj
  rcases hj with ⟨_hjrange, hjdrop⟩
  have hcell : (μ.colLen (j + 1), j) ∈ μ := by
    apply YoungDiagram.mem_iff_lt_colLen.mpr
    exact hjdrop
  have hrow_gt_j : j < μ.rowLen (μ.colLen (j + 1)) :=
    YoungDiagram.mem_iff_lt_rowLen.mp hcell
  have hnot_cell : ¬ (μ.colLen (j + 1), j + 1) ∈ μ := by
    intro hcell2
    have hlt := YoungDiagram.mem_iff_lt_colLen.mp hcell2
    omega
  have hrow_le : μ.rowLen (μ.colLen (j + 1)) ≤ j + 1 := by
    by_contra hnot
    have hgt : j + 1 < μ.rowLen (μ.colLen (j + 1)) := by omega
    exact hnot_cell (YoungDiagram.mem_iff_lt_rowLen.mpr hgt)
  omega

/-- A strict column-drop successor boundary can be read as a row boundary. -/
theorem rowBoundaryContent_colLen_succ_eq_colBoundaryContent_succ_of_colDrop
    (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ colDropIndicesBeforeRowDrop μ r) :
    rowBoundaryContent μ (μ.colLen (j + 1)) = colBoundaryContent μ (j + 1) := by
  have hrow := rowLen_colLen_succ_eq_succ_of_colDrop μ r hj
  dsimp [rowBoundaryContent, colBoundaryContent]
  rw [hrow]
  omega

/-- A nonzero addable row-boundary column below a fixed row drop is a strict column drop. -/
theorem rowLen_succ_pred_mem_colDropIndicesBeforeRowDrop_of_cornerRow_ge
    (μ : YoungDiagram) (r : CornerRows μ) {s : ℕ}
    (hs : s ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t)
    (hpos : 0 < μ.rowLen (s + 1)) :
    μ.rowLen (s + 1) - 1 ∈ colDropIndicesBeforeRowDrop μ r := by
  let j := μ.rowLen (s + 1) - 1
  have hcorner : s ∈ cornerRowIndices μ := (Finset.mem_filter.mp hs).1
  have hrle : r.1 ≤ s := (Finset.mem_filter.mp hs).2
  have hdrop_s : μ.rowLen (s + 1) < μ.rowLen s := (Finset.mem_filter.mp hcorner).2
  have hdrop_r : μ.rowLen (r.1 + 1) < μ.rowLen r.1 := (Finset.mem_filter.mp r.2).2
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter]
  constructor
  · apply Finset.mem_range.mpr
    have hle_succ : μ.rowLen (s + 1) ≤ μ.rowLen (r.1 + 1) := by
      exact μ.rowLen_anti (r.1 + 1) (s + 1) (by omega)
    dsimp [j, rowDropCornerCol]
    omega
  · change μ.colLen (j + 1) < μ.colLen j
    have hj_succ : j + 1 = μ.rowLen (s + 1) := by
      dsimp [j]
      omega
    have hcell_splus_j : (s + 1, j) ∈ μ := by
      apply YoungDiagram.mem_iff_lt_rowLen.mpr
      dsimp [j]
      omega
    have hcol_j_gt : s + 1 < μ.colLen j :=
      YoungDiagram.mem_iff_lt_colLen.mp hcell_splus_j
    have hcell_s_succ : (s, j + 1) ∈ μ := by
      apply YoungDiagram.mem_iff_lt_rowLen.mpr
      rw [hj_succ]
      exact hdrop_s
    have hcol_succ_gt : s < μ.colLen (j + 1) :=
      YoungDiagram.mem_iff_lt_colLen.mp hcell_s_succ
    have hnot_cell_splus_succ : ¬ (s + 1, j + 1) ∈ μ := by
      intro hcell
      have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hcell
      rw [hj_succ] at hrow
      omega
    have hcol_succ_le : μ.colLen (j + 1) ≤ s + 1 := by
      by_contra hnot
      have hgt : s + 1 < μ.colLen (j + 1) := by omega
      exact hnot_cell_splus_succ (YoungDiagram.mem_iff_lt_colLen.mpr hgt)
    omega

/-- Addable row-boundary columns below a fixed row drop land in the column boundary index set. -/
theorem rowLen_succ_mem_colAddableBoundaryIndicesBeforeRowDrop
    (μ : YoungDiagram) (r : CornerRows μ) {s : ℕ}
    (hs : s ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t) :
    μ.rowLen (s + 1) ∈ colAddableBoundaryIndicesBeforeRowDrop μ r := by
  by_cases hzero : μ.rowLen (s + 1) = 0
  · simp [colAddableBoundaryIndicesBeforeRowDrop, hzero]
  · have hpos : 0 < μ.rowLen (s + 1) := by omega
    have hdrop := rowLen_succ_pred_mem_colDropIndicesBeforeRowDrop_of_cornerRow_ge μ r hs hpos
    rw [colAddableBoundaryIndicesBeforeRowDrop]
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨μ.rowLen (s + 1) - 1, hdrop, ?_⟩
    omega

/-- The addable row-boundary column is injective on removable rows at or below a fixed row. -/
theorem rowLen_succ_injective_on_cornerRows_ge
    (μ : YoungDiagram) (r : CornerRows μ) {s₁ s₂ : ℕ}
    (hs₁ : s₁ ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t)
    (hs₂ : s₂ ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t)
    (h : μ.rowLen (s₁ + 1) = μ.rowLen (s₂ + 1)) :
    s₁ = s₂ := by
  have hcorner₁ : s₁ ∈ cornerRowIndices μ := (Finset.mem_filter.mp hs₁).1
  have hcorner₂ : s₂ ∈ cornerRowIndices μ := (Finset.mem_filter.mp hs₂).1
  rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
  · have hdrop₂ : μ.rowLen (s₂ + 1) < μ.rowLen s₂ := (Finset.mem_filter.mp hcorner₂).2
    have hle : μ.rowLen s₂ ≤ μ.rowLen (s₁ + 1) := by
      exact μ.rowLen_anti (s₁ + 1) s₂ (by omega)
    omega
  · exact heq
  · have hdrop₁ : μ.rowLen (s₁ + 1) < μ.rowLen s₁ := (Finset.mem_filter.mp hcorner₁).2
    have hle : μ.rowLen s₁ ≤ μ.rowLen (s₂ + 1) := by
      exact μ.rowLen_anti (s₂ + 1) s₁ (by omega)
    omega

/-- Lower addable-row numerator factors reindex as column-boundary factors. -/
theorem cornerRows_ge_succContentProd_eq_colAddableBoundaryIndices
    (μ : YoungDiagram) (r : CornerRows μ) :
    (((cornerRowIndices μ).filter fun s => r.1 ≤ s).prod
        (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ))) =
      (colAddableBoundaryIndicesBeforeRowDrop μ r).prod
        (fun k => ((rowDropContent μ r - colBoundaryContent μ k : ℤ) : ℚ)) := by
  apply Finset.prod_bij (fun s _hs => μ.rowLen (s + 1))
  · intro s hs
    exact rowLen_succ_mem_colAddableBoundaryIndicesBeforeRowDrop μ r hs
  · intro s₁ hs₁ s₂ hs₂ h
    exact rowLen_succ_injective_on_cornerRows_ge μ r hs₁ hs₂ h
  · intro k hk
    rw [colAddableBoundaryIndicesBeforeRowDrop] at hk
    rcases Finset.mem_insert.mp hk with hk0 | hkimg
    · subst k
      let s := μ.colLen 0 - 1
      have hs_corner : s ∈ cornerRowIndices μ := by
        simpa [s] using lastCornerRow_mem_cornerRowIndices μ r
      have hs_filter : s ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t := by
        rw [Finset.mem_filter]
        constructor
        · exact hs_corner
        · have hrange : r.1 ∈ Finset.range (μ.colLen 0) := (Finset.mem_filter.mp r.2).1
          have hrlt : r.1 < μ.colLen 0 := Finset.mem_range.mp hrange
          dsimp [s]
          omega
      refine ⟨s, hs_filter, ?_⟩
      have hrow := rowLen_colLen_zero_eq_zero μ
      have hpos : 0 < μ.colLen 0 := by
        have hrange : r.1 ∈ Finset.range (μ.colLen 0) := (Finset.mem_filter.mp r.2).1
        have hrlt : r.1 < μ.colLen 0 := Finset.mem_range.mp hrange
        omega
      have hs_succ : s + 1 = μ.colLen 0 := by
        dsimp [s]
        omega
      rw [hs_succ]
      exact hrow
    · rcases Finset.mem_image.mp hkimg with ⟨j, hj, hjk⟩
      let s := μ.colLen (j + 1) - 1
      have hs_filter : s ∈ (cornerRowIndices μ).filter fun t => r.1 ≤ t := by
        simpa [s] using colDropTopCornerRow_mem_cornerRowIndices_ge μ r hj
      refine ⟨s, hs_filter, ?_⟩
      have hpos : 0 < μ.colLen (j + 1) := by
        rw [colDropIndicesBeforeRowDrop, Finset.mem_filter] at hj
        rcases hj with ⟨hjrange, _hjdrop⟩
        have hjlt : j < rowDropCornerCol μ r := Finset.mem_range.mp hjrange
        have hcorner := rowDropCornerCol_lt_rowLen μ r
        have hr_cell : (r.1, j + 1) ∈ μ := by
          apply YoungDiagram.mem_iff_lt_rowLen.mpr
          dsimp [rowDropCornerCol] at hjlt hcorner
          omega
        have hcol := YoungDiagram.mem_iff_lt_colLen.mp hr_cell
        omega
      have hs_succ : s + 1 = μ.colLen (j + 1) := by
        dsimp [s]
        omega
      have hrow := rowLen_colLen_succ_eq_succ_of_colDrop μ r hj
      calc
        μ.rowLen (s + 1) = μ.rowLen (μ.colLen (j + 1)) := by rw [hs_succ]
        _ = j + 1 := hrow
        _ = k := hjk
  · intro s hs
    have hcorner : s ∈ cornerRowIndices μ := (Finset.mem_filter.mp hs).1
    change ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ) =
      ((rowDropContent μ r - colBoundaryContent μ (μ.rowLen (s + 1)) : ℤ) : ℚ)
    rw [rowBoundaryContent_succ_eq_colBoundaryContent_rowLen_succ_of_cornerRow μ hcorner]

/-- Lower addable-row numerator factors reindex as strict column-drop successor factors. -/
theorem cornerRows_ge_succContentProd_eq_colDropIndices
    (μ : YoungDiagram) (r : CornerRows μ) :
    (((cornerRowIndices μ).filter fun s => r.1 ≤ s).prod
        (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ))) =
      ((rowDropContent μ r - colBoundaryContent μ 0 : ℤ) : ℚ) *
        (colDropIndicesBeforeRowDrop μ r).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ (j + 1) : ℤ) : ℚ)) := by
  rw [cornerRows_ge_succContentProd_eq_colAddableBoundaryIndices]
  exact colAddableBoundaryIndicesBeforeRowDrop_prod_eq_zero_mul_succ μ r
    (fun k => ((rowDropContent μ r - colBoundaryContent μ k : ℤ) : ℚ))

/-- Filtering the column drops before a row-drop corner by the same upper bound changes nothing. -/
theorem colDropIndicesBeforeRowDrop_filter_lt (μ : YoungDiagram) (r : CornerRows μ) :
    ((colDropIndicesBeforeRowDrop μ r).filter fun j => j < rowDropCornerCol μ r) =
      colDropIndicesBeforeRowDrop μ r := by
  ext j
  simp only [colDropIndicesBeforeRowDrop, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h.1⟩

/-- The column of a row-drop corner has height one past the corner row. -/
theorem colLen_rowDropCornerCol (μ : YoungDiagram) (r : CornerRows μ) :
    μ.colLen (rowDropCornerCol μ r) = r.1 + 1 := by
  let hdrop : μ.rowLen (r.1 + 1) < μ.rowLen r.1 := (Finset.mem_filter.mp r.2).2
  have hc := colLen_corner μ (cornerCellOfRowDrop μ r.1 hdrop)
    (isCornerCell_cornerCellOfRowDrop μ r.1 hdrop)
  dsimp [cornerCellOfRowDrop, rowDropCornerCol] at hc
  simpa only [rowDropCornerCol] using hc

/-- Lower removable rows have strictly smaller corner columns. -/
theorem rowDropCornerCol_strictAnti (μ : YoungDiagram) {r s : CornerRows μ}
    (h : r.1 < s.1) :
    rowDropCornerCol μ s < rowDropCornerCol μ r := by
  have hr_drop : μ.rowLen (r.1 + 1) < μ.rowLen r.1 := (Finset.mem_filter.mp r.2).2
  have hle : μ.rowLen s.1 ≤ μ.rowLen (r.1 + 1) := by
    exact μ.rowLen_anti (r.1 + 1) s.1 (by omega)
  have hspos : 0 < μ.rowLen s.1 := by
    have hcorner := rowDropCornerCol_lt_rowLen μ s
    omega
  dsimp [rowDropCornerCol]
  omega

/-- Every row-drop corner column is also a strict column-height drop. -/
theorem colLen_succ_lt_colLen_rowDropCornerCol (μ : YoungDiagram) (r : CornerRows μ) :
    μ.colLen (rowDropCornerCol μ r + 1) < μ.colLen (rowDropCornerCol μ r) := by
  have hcol := colLen_rowDropCornerCol μ r
  have hnotcell : ¬ (r.1, rowDropCornerCol μ r + 1) ∈ μ := by
    intro hcell
    have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hcorner := rowDropCornerCol_lt_rowLen μ r
    dsimp [rowDropCornerCol] at hrow hcorner
    omega
  have hle : μ.colLen (rowDropCornerCol μ r + 1) ≤ r.1 := by
    by_contra hnot
    have hgt : r.1 < μ.colLen (rowDropCornerCol μ r + 1) := by omega
    have hcell : (r.1, rowDropCornerCol μ r + 1) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr hgt
    exact hnotcell hcell
  omega

/-- A lower removable row contributes a column drop before the fixed removable row. -/
theorem rowDropCornerCol_mem_colDropIndicesBeforeRowDrop_of_lt
    (μ : YoungDiagram) (r s : CornerRows μ) (h : r.1 < s.1) :
    rowDropCornerCol μ s ∈ colDropIndicesBeforeRowDrop μ r := by
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (rowDropCornerCol_strictAnti μ h),
    colLen_succ_lt_colLen_rowDropCornerCol μ s⟩

/-- A strict column drop before a fixed removable row identifies a lower removable row. -/
theorem colDropCornerRow_mem_cornerRowIndices_of_mem
    (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ colDropIndicesBeforeRowDrop μ r) :
    μ.colLen j - 1 ∈ (cornerRowIndices μ).filter fun s => r.1 < s := by
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter] at hj
  rcases hj with ⟨hjrange, hjdrop⟩
  have hjlt : j < rowDropCornerCol μ r := Finset.mem_range.mp hjrange
  have hcolpos : 0 < μ.colLen j := by omega
  let s := μ.colLen j - 1
  have hs_lt_col : s < μ.colLen j := by
    dsimp [s]
    omega
  have hs_cell_j : (s, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hs_lt_col
  have hrow_gt_j : j < μ.rowLen s := YoungDiagram.mem_iff_lt_rowLen.mp hs_cell_j
  have hcolsucc_le : μ.colLen (j + 1) ≤ s := by
    dsimp [s]
    omega
  have hnot_cell_s_succ : ¬ (s, j + 1) ∈ μ := by
    intro hcell
    have hslt := YoungDiagram.mem_iff_lt_colLen.mp hcell
    omega
  have hrow_le_succ : μ.rowLen s ≤ j + 1 := by
    by_contra hnot
    have hgt : j + 1 < μ.rowLen s := by omega
    exact hnot_cell_s_succ (YoungDiagram.mem_iff_lt_rowLen.mpr hgt)
  have hrow_eq : μ.rowLen s = j + 1 := by omega
  have hnot_cell_next_j : ¬ (s + 1, j) ∈ μ := by
    intro hcell
    have hslt := YoungDiagram.mem_iff_lt_colLen.mp hcell
    dsimp [s] at hslt
    omega
  have hrow_next_le : μ.rowLen (s + 1) ≤ j := by
    by_contra hnot
    have hgt : j < μ.rowLen (s + 1) := by omega
    exact hnot_cell_next_j (YoungDiagram.mem_iff_lt_rowLen.mpr hgt)
  have hrowdrop : μ.rowLen (s + 1) < μ.rowLen s := by omega
  have hr_lt_s : r.1 < s := by
    have hcorner := rowDropCornerCol_lt_rowLen μ r
    have hjlt_row : j < μ.rowLen r.1 - 1 := by
      simpa [rowDropCornerCol] using hjlt
    have hcorner_row : μ.rowLen r.1 - 1 < μ.rowLen r.1 := by
      simpa [rowDropCornerCol] using hcorner
    have hr_cell : (r.1, j + 1) ∈ μ := by
      apply YoungDiagram.mem_iff_lt_rowLen.mpr
      omega
    have hr_lt_colsucc : r.1 < μ.colLen (j + 1) :=
      YoungDiagram.mem_iff_lt_colLen.mp hr_cell
    omega
  rw [Finset.mem_filter]
  constructor
  · rw [cornerRowIndices, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hcolle : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti 0 j (Nat.zero_le j)
      omega
    · simpa [s] using hrowdrop
  · simpa [s] using hr_lt_s

/-- The current row-drop content is one above the corner column-boundary content. -/
theorem rowDropContent_sub_colBoundaryContent_corner (μ : YoungDiagram) (r : CornerRows μ) :
    rowDropContent μ r - colBoundaryContent μ (rowDropCornerCol μ r) = 1 := by
  have hcol := colLen_rowDropCornerCol μ r
  have hcol_eq : μ.colLen (μ.rowLen r.1 - 1) = r.1 + 1 := by
    simpa [rowDropCornerCol] using hcol
  dsimp [rowDropContent, colBoundaryContent, rowDropCornerCol]
  rw [hcol_eq]
  omega

/-- At a strict column drop before a row-drop corner, the bottom row has length `j + 1`. -/
theorem rowLen_colDropCornerRow_eq_succ
    (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ colDropIndicesBeforeRowDrop μ r) :
    μ.rowLen (μ.colLen j - 1) = j + 1 := by
  rw [colDropIndicesBeforeRowDrop, Finset.mem_filter] at hj
  rcases hj with ⟨_hjrange, hjdrop⟩
  have hcolpos : 0 < μ.colLen j := by omega
  let s := μ.colLen j - 1
  have hs_lt_col : s < μ.colLen j := by
    dsimp [s]
    omega
  have hs_cell_j : (s, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hs_lt_col
  have hrow_gt_j : j < μ.rowLen s := YoungDiagram.mem_iff_lt_rowLen.mp hs_cell_j
  have hcolsucc_le : μ.colLen (j + 1) ≤ s := by
    dsimp [s]
    omega
  have hnot_cell_s_succ : ¬ (s, j + 1) ∈ μ := by
    intro hcell
    have hslt := YoungDiagram.mem_iff_lt_colLen.mp hcell
    omega
  have hrow_le_succ : μ.rowLen s ≤ j + 1 := by
    by_contra hnot
    have hgt : j + 1 < μ.rowLen s := by omega
    exact hnot_cell_s_succ (YoungDiagram.mem_iff_lt_rowLen.mpr hgt)
  have hrow_eq : μ.rowLen s = j + 1 := by omega
  simpa [s] using hrow_eq

/-- Lower removable-row denominator factors reindex as strict column-drop factors. -/
theorem cornerRows_gt_denContentProd_eq_colDropIndices
    (μ : YoungDiagram) (r : CornerRows μ) :
    (((cornerRowIndices μ).filter fun s => r.1 < s).prod
        (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) =
      (colDropIndicesBeforeRowDrop μ r).prod
        (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ)) := by
  apply Finset.prod_bij (fun s hs =>
    rowDropCornerCol μ ⟨s, (Finset.mem_filter.mp hs).1⟩)
  · intro s hs
    exact rowDropCornerCol_mem_colDropIndicesBeforeRowDrop_of_lt μ r
      ⟨s, (Finset.mem_filter.mp hs).1⟩ (Finset.mem_filter.mp hs).2
  · intro s1 hs1 s2 hs2 h
    let c1 : CornerRows μ := ⟨s1, (Finset.mem_filter.mp hs1).1⟩
    let c2 : CornerRows μ := ⟨s2, (Finset.mem_filter.mp hs2).1⟩
    have h1 := colLen_rowDropCornerCol μ c1
    have h2 := colLen_rowDropCornerCol μ c2
    have hs12 : s1 + 1 = s2 + 1 := by
      calc
        s1 + 1 = μ.colLen (rowDropCornerCol μ c1) := h1.symm
        _ = μ.colLen (rowDropCornerCol μ c2) := by rw [h]
        _ = s2 + 1 := h2
    omega
  · intro j hj
    let s := μ.colLen j - 1
    have hsfilter : s ∈ (cornerRowIndices μ).filter fun s => r.1 < s := by
      simpa [s] using colDropCornerRow_mem_cornerRowIndices_of_mem μ r hj
    refine ⟨s, hsfilter, ?_⟩
    have hrow := rowLen_colDropCornerRow_eq_succ μ r hj
    dsimp [s, rowDropCornerCol]
    omega
  · intro s hs
    let cs : CornerRows μ := ⟨s, (Finset.mem_filter.mp hs).1⟩
    change ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ) =
      ((rowDropContent μ r - colBoundaryContent μ (rowDropCornerCol μ cs) - 1 : ℤ) : ℚ)
    have hbd : rowBoundaryContent μ s - 1 = rowDropContent μ cs := by
      exact (rowDropContent_eq_rowBoundaryContent_sub_one μ cs).symm
    have hcol : rowDropContent μ cs = colBoundaryContent μ (rowDropCornerCol μ cs) + 1 := by
      have h := rowDropContent_sub_colBoundaryContent_corner μ cs
      omega
    rw [hbd, hcol]
    ring_nf

/--
Column boundary contents left of a fixed removable row telescope, leaving only
the strict column-drop boundary factors.
-/
theorem colBoundaryContent_prod_telescope_before_corner
    (μ : YoungDiagram) (r : CornerRows μ) :
    ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j : ℤ) : ℚ))) *
        ((colDropIndicesBeforeRowDrop μ r).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))) =
      ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))) *
        (((rowDropContent μ r - colBoundaryContent μ 0 : ℤ) : ℚ) *
          ((colDropIndicesBeforeRowDrop μ r).prod
            (fun j => ((rowDropContent μ r - colBoundaryContent μ (j + 1) : ℤ) : ℚ)))) := by
  have htel := prod_Ico_telescope_with_drops (colDropIndicesBeforeRowDrop μ r) (M := ℚ)
    (fun j => ((rowDropContent μ r - colBoundaryContent μ j : ℤ) : ℚ))
    (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))
    (rowDropCornerCol μ r) ?_
  · rw [colDropIndicesBeforeRowDrop_filter_lt] at htel
    have hself :
        (((rowDropContent μ r - colBoundaryContent μ (rowDropCornerCol μ r) : ℤ) : ℚ)) =
          1 := by
      exact_mod_cast rowDropContent_sub_colBoundaryContent_corner μ r
    rw [hself, one_mul] at htel
    simpa [mul_assoc] using htel
  · intro j hj hnot
    have hjrange : j ∈ Finset.range (rowDropCornerCol μ r) := Finset.mem_range.mpr hj
    have hnotdrop : ¬ μ.colLen (j + 1) < μ.colLen j := by
      intro hdrop
      exact hnot (by simp [colDropIndicesBeforeRowDrop, hjrange, hdrop])
    change (((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ)) =
      ((rowDropContent μ r - colBoundaryContent μ (j + 1) : ℤ) : ℚ)
    rw [colBoundaryContent_succ_eq_add_one_of_not_drop μ hnotdrop]
    ring_nf

/-- Row-drop contents strictly decrease as their row indices increase. -/
theorem rowDropContent_strictAnti (μ : YoungDiagram) {r s : CornerRows μ}
    (h : r.1 < s.1) :
    rowDropContent μ s < rowDropContent μ r := by
  rw [rowDropContent_eq_rowBoundaryContent_sub_one,
    rowDropContent_eq_rowBoundaryContent_sub_one]
  have hrow := rowBoundaryContent_strictAnti μ h
  omega

/-- Row-drop content is injective as a function of the row-drop index. -/
theorem rowDropContent_injective (μ : YoungDiagram) :
    Function.Injective (rowDropContent μ) := by
  intro r s h
  apply Subtype.ext
  rcases lt_trichotomy r.1 s.1 with hlt | heq | hgt
  · have hstrict := rowDropContent_strictAnti μ hlt
    omega
  · exact heq
  · have hstrict := rowDropContent_strictAnti μ hgt
    omega

/-- Row numerator factors are content differences after casting to integers. -/
theorem rowDropInterval_rowNumFactor_int (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    (((rowDropCornerCol μ r - j) + (μ.colLen j - r.1) : ℕ) : ℤ) =
      rowDropContent μ r - colBoundaryContent μ j := by
  have hjlt : j < rowDropCornerCol μ r := (Finset.mem_Ico.mp hj).2
  have hcollt : r.1 < μ.colLen j := by
    have hjrow : j < μ.rowLen r.1 := by
      have hcorner := rowDropCornerCol_lt_rowLen μ r
      omega
    have hcell : (r.1, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hjrow
    exact YoungDiagram.mem_iff_lt_colLen.mp hcell
  dsimp [rowDropContent, colBoundaryContent]
  omega

/-- Row denominator factors are shifted content differences after casting to integers. -/
theorem rowDropInterval_rowDenFactor_int (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    (((rowDropCornerCol μ r - j) + (μ.colLen j - r.1) - 1 : ℕ) : ℤ) =
      rowDropContent μ r - colBoundaryContent μ j - 1 := by
  have hjlt : j < rowDropCornerCol μ r := (Finset.mem_Ico.mp hj).2
  have hcollt : r.1 < μ.colLen j := by
    have hjrow : j < μ.rowLen r.1 := by
      have hcorner := rowDropCornerCol_lt_rowLen μ r
      omega
    have hcell : (r.1, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hjrow
    exact YoungDiagram.mem_iff_lt_colLen.mp hcell
  dsimp [rowDropContent, colBoundaryContent]
  omega

/-- Column numerator factors are content differences after casting to integers. -/
theorem rowDropInterval_colNumFactor_int (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i ∈ Finset.Ico 0 r.1) :
    (((μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) : ℕ) : ℤ) =
      rowBoundaryContent μ i - rowDropContent μ r := by
  have hilt : i < r.1 := (Finset.mem_Ico.mp hi).2
  have hirow : rowDropCornerCol μ r < μ.rowLen i := by
    have hcorner_col_lt : rowDropCornerCol μ r < μ.rowLen r.1 :=
      rowDropCornerCol_lt_rowLen μ r
    have hcorner_mem : (r.1, rowDropCornerCol μ r) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hcorner_col_lt
    have hi_mem : (i, rowDropCornerCol μ r) ∈ μ :=
      μ.up_left_mem (Nat.le_of_lt hilt) le_rfl hcorner_mem
    exact YoungDiagram.mem_iff_lt_rowLen.mp hi_mem
  dsimp [rowBoundaryContent, rowDropContent]
  omega

/-- Column denominator factors are shifted content differences after casting to integers. -/
theorem rowDropInterval_colDenFactor_int (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i ∈ Finset.Ico 0 r.1) :
    (((μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) - 1 : ℕ) : ℤ) =
      rowBoundaryContent μ i - rowDropContent μ r - 1 := by
  have hilt : i < r.1 := (Finset.mem_Ico.mp hi).2
  have hirow : rowDropCornerCol μ r < μ.rowLen i := by
    have hcorner_col_lt : rowDropCornerCol μ r < μ.rowLen r.1 :=
      rowDropCornerCol_lt_rowLen μ r
    have hcorner_mem : (r.1, rowDropCornerCol μ r) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hcorner_col_lt
    have hi_mem : (i, rowDropCornerCol μ r) ∈ μ :=
      μ.up_left_mem (Nat.le_of_lt hilt) le_rfl hcorner_mem
    exact YoungDiagram.mem_iff_lt_rowLen.mp hi_mem
  dsimp [rowBoundaryContent, rowDropContent]
  omega

/-- Column boundary contents to the left lie below the row-drop content. -/
theorem colBoundaryContent_lt_rowDropContent (μ : YoungDiagram) (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    colBoundaryContent μ j < rowDropContent μ r := by
  have hpos : (0 : ℤ) <
      (((rowDropCornerCol μ r - j) + (μ.colLen j - r.1) : ℕ) : ℤ) := by
    exact_mod_cast rowDropInterval_rowNumFactor_pos μ r hj
  rw [rowDropInterval_rowNumFactor_int μ r hj] at hpos
  omega

/-- Shifted column boundary contents to the left still lie below the row-drop content. -/
theorem colBoundaryContent_add_one_lt_rowDropContent (μ : YoungDiagram)
    (r : CornerRows μ) {j : ℕ}
    (hj : j ∈ Finset.Ico 0 (rowDropCornerCol μ r)) :
    colBoundaryContent μ j + 1 < rowDropContent μ r := by
  have hpos : (0 : ℤ) <
      (((rowDropCornerCol μ r - j) + (μ.colLen j - r.1) - 1 : ℕ) : ℤ) := by
    exact_mod_cast rowDropInterval_rowDenFactor_pos μ r hj
  rw [rowDropInterval_rowDenFactor_int μ r hj] at hpos
  omega

/-- Row boundary contents above lie above the row-drop content. -/
theorem rowDropContent_lt_rowBoundaryContent (μ : YoungDiagram) (r : CornerRows μ) {i : ℕ}
    (hi : i ∈ Finset.Ico 0 r.1) :
    rowDropContent μ r < rowBoundaryContent μ i := by
  have hpos : (0 : ℤ) <
      (((μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) : ℕ) : ℤ) := by
    exact_mod_cast rowDropInterval_colNumFactor_pos μ r hi
  rw [rowDropInterval_colNumFactor_int μ r hi] at hpos
  omega

/-- Row boundary contents above still lie above the shifted row-drop content. -/
theorem rowDropContent_add_one_lt_rowBoundaryContent (μ : YoungDiagram)
    (r : CornerRows μ) {i : ℕ} (hi : i ∈ Finset.Ico 0 r.1) :
    rowDropContent μ r + 1 < rowBoundaryContent μ i := by
  have hpos : (0 : ℤ) <
      (((μ.rowLen i - rowDropCornerCol μ r) + (r.1 - i) - 1 : ℕ) : ℤ) := by
    exact_mod_cast rowDropInterval_colDenFactor_pos μ r hi
  rw [rowDropInterval_colDenFactor_int μ r hi] at hpos
  omega

/-- The row-drop numerator product is a product of integer content differences. -/
theorem hookProductRowDropIntervalNumerator_int (μ : YoungDiagram) (r : CornerRows μ) :
    ((hookProductRowDropIntervalNumerator μ r : ℕ) : ℤ) =
      ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => rowDropContent μ r - colBoundaryContent μ j)) *
        ((Finset.Ico 0 r.1).prod
          (fun i => rowBoundaryContent μ i - rowDropContent μ r)) := by
  dsimp [hookProductRowDropIntervalNumerator]
  rw [Finset.prod_natCast, Finset.prod_natCast]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    exact rowDropInterval_rowNumFactor_int μ r hj
  · apply Finset.prod_congr rfl
    intro i hi
    exact rowDropInterval_colNumFactor_int μ r hi

/-- The row-drop denominator product is a product of shifted integer content differences. -/
theorem hookProductRowDropIntervalDenominator_int (μ : YoungDiagram) (r : CornerRows μ) :
    ((hookProductRowDropIntervalDenominator μ r : ℕ) : ℤ) =
      ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => rowDropContent μ r - colBoundaryContent μ j - 1)) *
        ((Finset.Ico 0 r.1).prod
          (fun i => rowBoundaryContent μ i - rowDropContent μ r - 1)) := by
  dsimp [hookProductRowDropIntervalDenominator]
  rw [Finset.prod_natCast, Finset.prod_natCast]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    exact rowDropInterval_rowDenFactor_int μ r hj
  · apply Finset.prod_congr rfl
    intro i hi
    exact rowDropInterval_colDenFactor_int μ r hi

/-- Rational version of the row-drop numerator content product. -/
theorem hookProductRowDropIntervalNumerator_rat (μ : YoungDiagram) (r : CornerRows μ) :
    ((hookProductRowDropIntervalNumerator μ r : ℕ) : ℚ) =
      ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j : ℤ) : ℚ))) *
        ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))) := by
  rw [← Int.cast_prod, ← Int.cast_prod]
  exact_mod_cast hookProductRowDropIntervalNumerator_int μ r

/-- Rational version of the row-drop denominator content product. -/
theorem hookProductRowDropIntervalDenominator_rat (μ : YoungDiagram) (r : CornerRows μ) :
    ((hookProductRowDropIntervalDenominator μ r : ℕ) : ℚ) =
      ((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))) *
        ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))) := by
  rw [← Int.cast_prod, ← Int.cast_prod]
  exact_mod_cast hookProductRowDropIntervalDenominator_int μ r

/-- The row-drop rational summand rewritten as content-difference products. -/
theorem hookProductRowDropIntervalRatio_eq_contentProducts (μ : YoungDiagram)
    (r : CornerRows μ) :
    hookProductRowDropIntervalRatio μ r =
      (((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j : ℤ) : ℚ))) *
        ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ)))) /
      (((Finset.Ico 0 (rowDropCornerCol μ r)).prod
          (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))) *
        ((Finset.Ico 0 r.1).prod
          (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ)))) := by
  rw [hookProductRowDropIntervalRatio, hookProductRowDropIntervalNumerator_rat,
    hookProductRowDropIntervalDenominator_rat]

/-- Addable-row content products rewritten over the underlying row-index finset. -/
theorem addableRows_contentProd_eq (μ : YoungDiagram) (r : CornerRows μ) :
    (Finset.univ.prod fun a : AddableRows μ =>
        ((rowDropContent μ r - rowBoundaryContent μ a.1 : ℤ) : ℚ)) =
      (addableRowIndices μ).prod
        (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ)) := by
  exact addableRows_prod_eq (M := ℚ) μ
    (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ))

/-- Removable-row content products except one row drop rewritten over row-index finsets. -/
theorem cornerRows_filter_contentProd_eq (μ : YoungDiagram) (r : CornerRows μ) :
    ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod fun s =>
      ((rowDropContent μ r - rowDropContent μ s : ℤ) : ℚ)) =
    (((cornerRowIndices μ).filter fun s => s ≠ r.1).prod
      (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) := by
  rw [show ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod fun s =>
      ((rowDropContent μ r - rowDropContent μ s : ℤ) : ℚ)) =
      ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod fun s =>
      ((rowDropContent μ r - (rowBoundaryContent μ s.1 - 1) : ℤ) : ℚ)) by
    apply Finset.prod_congr rfl
    intro s _hs
    rw [rowDropContent_eq_rowBoundaryContent_sub_one μ s]]
  exact cornerRows_filter_ne_prod_eq μ r
    (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))

/-- Addable content products split into the top row and successor corner rows. -/
theorem addableRowIndices_contentProd_eq_zero_mul_succ
    (μ : YoungDiagram) (r : CornerRows μ) :
    (addableRowIndices μ).prod
        (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ)) =
      ((rowDropContent μ r - rowBoundaryContent μ 0 : ℤ) : ℚ) *
        (cornerRowIndices μ).prod
          (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ)) := by
  exact addableRowIndices_prod_eq_zero_mul_succ μ
    (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ))

/-- Filtered removable content products split into row drops above and below the current one. -/
theorem cornerRowIndices_filter_contentProd_eq_lt_mul_gt
    (μ : YoungDiagram) (r : CornerRows μ) :
    (((cornerRowIndices μ).filter fun s => s ≠ r.1).prod
        (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) =
      (((cornerRowIndices μ).filter fun s => s < r.1).prod
          (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) *
        (((cornerRowIndices μ).filter fun s => r.1 < s).prod
          (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) := by
  exact cornerRowIndices_filter_ne_prod_eq_lt_mul_gt μ r
    (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))

/-- Addable/removable content product expected for a row-drop summand. -/
noncomputable def hookProductRowDropContentRatio (μ : YoungDiagram) (r : CornerRows μ) : ℚ :=
  -(((Finset.univ : Finset (AddableRows μ)).prod
      (fun a => ((rowDropContent μ r - rowBoundaryContent μ a.1 : ℤ) : ℚ))) /
    ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod
      (fun s => ((rowDropContent μ r - rowDropContent μ s : ℤ) : ℚ))))

/-- The removable-content denominator in the content ratio is nonzero. -/
theorem hookProductRowDropContentDenominator_ne_zero (μ : YoungDiagram)
    (r : CornerRows μ) :
    ((Finset.univ.filter fun s : CornerRows μ => s ≠ r).prod
      (fun s => ((rowDropContent μ r - rowDropContent μ s : ℤ) : ℚ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  have hsne : s ≠ r := (Finset.mem_filter.mp hs).2
  have hcontents : rowDropContent μ r ≠ rowDropContent μ s := by
    intro h
    exact hsne ((rowDropContent_injective μ) h.symm)
  exact_mod_cast (sub_ne_zero.mpr hcontents)

/-- The content-ratio summand rewritten over the underlying addable/removable index sets. -/
theorem hookProductRowDropContentRatio_eq_indexProducts
    (μ : YoungDiagram) (r : CornerRows μ) :
    hookProductRowDropContentRatio μ r =
      -(((addableRowIndices μ).prod
          (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ))) /
        (((cornerRowIndices μ).filter fun s => s ≠ r.1).prod
          (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ)))) := by
  rw [hookProductRowDropContentRatio]
  rw [addableRows_contentProd_eq]
  rw [cornerRows_filter_contentProd_eq]

/-- The interval row-drop summand equals the addable/removable index-product shape. -/
theorem hookProductRowDropIntervalRatio_eq_indexProducts
    (μ : YoungDiagram) (r : CornerRows μ) :
    hookProductRowDropIntervalRatio μ r =
      -(((addableRowIndices μ).prod
          (fun a => ((rowDropContent μ r - rowBoundaryContent μ a : ℤ) : ℚ))) /
        (((cornerRowIndices μ).filter fun s => s ≠ r.1).prod
          (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ)))) := by
  let CN := (Finset.Ico 0 (rowDropCornerCol μ r)).prod
    (fun j => ((rowDropContent μ r - colBoundaryContent μ j : ℤ) : ℚ))
  let CD := (Finset.Ico 0 (rowDropCornerCol μ r)).prod
    (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))
  let RN := (Finset.Ico 0 r.1).prod
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r : ℤ) : ℚ))
  let RD := (Finset.Ico 0 r.1).prod
    (fun i => ((rowBoundaryContent μ i - rowDropContent μ r - 1 : ℤ) : ℚ))
  let Top := ((rowBoundaryContent μ 0 - rowDropContent μ r : ℤ) : ℚ)
  let TopContent := ((rowDropContent μ r - rowBoundaryContent μ 0 : ℤ) : ℚ)
  let SLt := (((cornerRowIndices μ).filter fun s => s < r.1).prod
    (fun s => ((rowDropContent μ r - rowBoundaryContent μ (s + 1) : ℤ) : ℚ)))
  let SGe := ((rowDropContent μ r - colBoundaryContent μ 0 : ℤ) : ℚ) *
    (colDropIndicesBeforeRowDrop μ r).prod
      (fun j => ((rowDropContent μ r - colBoundaryContent μ (j + 1) : ℤ) : ℚ))
  let DLt := (((cornerRowIndices μ).filter fun s => s < r.1).prod
    (fun s => ((rowDropContent μ r - (rowBoundaryContent μ s - 1) : ℤ) : ℚ)))
  let DGt := (colDropIndicesBeforeRowDrop μ r).prod
    (fun j => ((rowDropContent μ r - colBoundaryContent μ j - 1 : ℤ) : ℚ))
  have hrow : RN * DLt = RD * (Top * SLt) := by
    simpa [RN, RD, Top, SLt, DLt] using
      rowBoundaryContent_prod_telescope_before_corner_content μ r
  have hcol : CN * DGt = CD * SGe := by
    simpa [CN, CD, DGt, SGe] using colBoundaryContent_prod_telescope_before_corner μ r
  have htop : TopContent = -Top := by
    dsimp [TopContent, Top]
    exact_mod_cast (show rowDropContent μ r - rowBoundaryContent μ 0 =
      -(rowBoundaryContent μ 0 - rowDropContent μ r) by ring)
  have hdenInt : CD * RD ≠ 0 := by
    have h := hookProductRowDropIntervalDenominator_ne_zero μ r
    rw [hookProductRowDropIntervalDenominator_rat] at h
    simpa [CD, RD] using h
  have hdenContent : DLt * DGt ≠ 0 := by
    have h := hookProductRowDropContentDenominator_ne_zero μ r
    rw [cornerRows_filter_contentProd_eq, cornerRowIndices_filter_contentProd_eq_lt_mul_gt,
      cornerRows_gt_denContentProd_eq_colDropIndices] at h
    simpa [DLt, DGt] using h
  have hDLt : DLt ≠ 0 := (mul_ne_zero_iff.mp hdenContent).1
  have hDGt : DGt ≠ 0 := (mul_ne_zero_iff.mp hdenContent).2
  rw [hookProductRowDropIntervalRatio_eq_contentProducts]
  rw [addableRowIndices_contentProd_eq_zero_mul_succ]
  rw [cornerRowIndices_prod_eq_lt_mul_ge]
  rw [cornerRows_ge_succContentProd_eq_colDropIndices]
  rw [cornerRowIndices_filter_contentProd_eq_lt_mul_gt]
  rw [cornerRows_gt_denContentProd_eq_colDropIndices]
  change CN * RN / (CD * RD) = -(TopContent * (SLt * SGe) / (DLt * DGt))
  rw [div_eq_iff hdenInt]
  rw [htop]
  ring_nf
  field_simp [hDLt, hDGt]
  calc
    CN * RN * DLt * DGt = (CN * DGt) * (RN * DLt) := by ring
    _ = (CD * SGe) * (RD * (Top * SLt)) := by rw [hcol, hrow]
    _ = Top * SLt * SGe * CD * RD := by ring

/-- Product-compression target from interval products to addable/removable content products. -/
def HookProductRowDropContentProductFormula : Prop :=
  ∀ μ : YoungDiagram, ∀ r : CornerRows μ,
    hookProductRowDropIntervalRatio μ r = hookProductRowDropContentRatio μ r

/-- Checked interval-to-content product formula for every row-drop summand. -/
theorem hookProductRowDropContentProductFormula :
    HookProductRowDropContentProductFormula := by
  intro μ r
  rw [hookProductRowDropIntervalRatio_eq_indexProducts,
    hookProductRowDropContentRatio_eq_indexProducts]

/-- Pure content finite-sum target for the row-drop branching identity. -/
def HookProductBranchingContentIdentity : Prop :=
  ∀ μ : YoungDiagram, μ.cells.Nonempty →
    (Finset.univ.sum fun r : CornerRows μ => hookProductRowDropContentRatio μ r) =
      (μ.card : ℚ)

/-- Checked pure content finite-sum identity for the row-drop branching formula. -/
theorem hookProductBranchingContentIdentity :
    HookProductBranchingContentIdentity := by
  classical
  intro μ hμ
  let A := addableRowIndices μ
  let B := cornerRowIndices μ
  let y : ℕ → ℚ := fun a => ((rowBoundaryContent μ a : ℤ) : ℚ)
  let x : ℕ → ℚ := fun r => ((rowBoundaryContent μ r - 1 : ℤ) : ℚ)
  have hB : B.Nonempty := by
    obtain ⟨c, hc⟩ := exists_isCornerCell_of_nonempty μ hμ
    let r : CornerRows μ := (cornerRowsEquivCornerCells μ).symm ⟨c, hc⟩
    exact ⟨r.1, r.2⟩
  have hcard : A.card = B.card + 1 := by
    dsimp [A, B]
    exact addableRowIndices_card μ
  have hinj : Set.InjOn x B := by
    intro a ha b hb h
    dsimp [x] at h
    have hInt : rowBoundaryContent μ a - 1 = rowBoundaryContent μ b - 1 := by
      exact_mod_cast h
    have hrow : rowBoundaryContent μ a = rowBoundaryContent μ b := by omega
    exact rowBoundaryContent_injective μ hrow
  have hsum : A.sum y = B.sum x := by
    dsimp [A, B, x, y]
    exact_mod_cast addableRowIndices_sum_rowBoundaryContent_eq_cornerRowIndices_sum_rowDropContent μ
  have hlag := lagrange_sum_prod_div_eq A B y x hB hcard hinj hsum
  have hratio :
      (Finset.univ.sum fun r : CornerRows μ => hookProductRowDropContentRatio μ r) =
        B.sum (fun r => -((A.prod (fun a => x r - y a)) /
          ((B.erase r).prod (fun s => x r - x s)))) := by
    rw [Finset.univ_eq_attach (cornerRowIndices μ)]
    let F : ℕ → ℚ := fun r =>
      if hr : r ∈ cornerRowIndices μ then hookProductRowDropContentRatio μ ⟨r, hr⟩ else 0
    have hattach :
        (∑ r ∈ (cornerRowIndices μ).attach, hookProductRowDropContentRatio μ r) =
          ∑ r ∈ (cornerRowIndices μ).attach, F r := by
      apply Finset.sum_congr rfl
      intro r _hr
      dsimp [F]
      simp [r.property]
    rw [hattach]
    rw [Finset.sum_attach (cornerRowIndices μ) F]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [F]
    simp [hr]
    have hratio_r := hookProductRowDropContentRatio_eq_indexProducts μ ⟨r, hr⟩
    rw [hratio_r]
    dsimp [A, B, x, y]
    have hnum :
        (addableRowIndices μ).prod
            (fun a => ((rowDropContent μ ⟨r, hr⟩ - rowBoundaryContent μ a : ℤ) : ℚ)) =
          (addableRowIndices μ).prod
            (fun a => ((rowBoundaryContent μ r - 1 : ℤ) : ℚ) -
              ((rowBoundaryContent μ a : ℤ) : ℚ)) := by
      apply Finset.prod_congr rfl
      intro a _ha
      rw [rowDropContent_eq_rowBoundaryContent_sub_one]
      exact_mod_cast (show rowBoundaryContent μ r - 1 - rowBoundaryContent μ a =
        (rowBoundaryContent μ r - 1) - rowBoundaryContent μ a by ring)
    have hden :
        (((cornerRowIndices μ).filter fun s => s ≠ r).prod
            (fun s =>
              ((rowDropContent μ ⟨r, hr⟩ - (rowBoundaryContent μ s - 1) : ℤ) : ℚ))) =
          ((cornerRowIndices μ).erase r).prod
            (fun s => ((rowBoundaryContent μ r - 1 : ℤ) : ℚ) -
              ((rowBoundaryContent μ s - 1 : ℤ) : ℚ)) := by
      have herase :
          (cornerRowIndices μ).filter (fun s => s ≠ r) =
            (cornerRowIndices μ).erase r := by
        ext s
        simp [and_comm, eq_comm]
      rw [herase]
      apply Finset.prod_congr rfl
      intro s _hs
      rw [rowDropContent_eq_rowBoundaryContent_sub_one]
      exact_mod_cast
        (show rowBoundaryContent μ (↑(⟨r, hr⟩ : CornerRows μ)) - 1 -
              (rowBoundaryContent μ s - 1) =
            rowBoundaryContent μ r - 1 - (rowBoundaryContent μ s - 1) by
          rfl)
    rw [hnum, hden]
  rw [hratio]
  rw [Finset.sum_neg_distrib]
  rw [hlag]
  have hsq : A.sum (fun a => y a ^ 2) - B.sum (fun r => x r ^ 2) =
      (2 : ℚ) * (μ.card : ℚ) := by
    dsimp [A, B, x, y]
    exact_mod_cast
      addableRowIndices_sum_sq_rowBoundaryContent_sub_cornerRowIndices_sum_sq_eq_card μ
  linarith

/-- The content product route implies the row-drop interval branching identity. -/
theorem hookProductBranchingRowDropIntervalIdentity_of_content
    (hformula : HookProductRowDropContentProductFormula)
    (hcontent : HookProductBranchingContentIdentity) :
    HookProductBranchingRowDropIntervalIdentity := by
  intro μ hμ
  rw [show (Finset.univ.sum fun r : CornerRows μ => hookProductRowDropIntervalRatio μ r) =
      Finset.univ.sum (fun r : CornerRows μ => hookProductRowDropContentRatio μ r) by
    apply Finset.sum_congr rfl
    intro r _hr
    exact hformula μ r]
  exact hcontent μ hμ

/-- The branching identity is equivalent to its interval-product form. -/
theorem hookProductBranchingIdentity_iff_interval :
    HookProductBranchingIdentity ↔ HookProductBranchingIntervalIdentity := by
  unfold HookProductBranchingIdentity HookProductBranchingIntervalIdentity
  constructor
  · intro h μ hμ
    rw [← h μ hμ]
    apply Finset.sum_congr rfl
    intro c _hc
    exact (hookProductCornerRatio_eq_interval μ c).symm
  · intro h μ hμ
    rw [← h μ hμ]
    apply Finset.sum_congr rfl
    intro c _hc
    exact hookProductCornerRatio_eq_interval μ c

/-- The branching identity is equivalent to its finite row-drop summation form. -/
theorem hookProductBranchingIdentity_iff_rowDrops :
    HookProductBranchingIdentity ↔ HookProductBranchingRowDropIdentity := by
  unfold HookProductBranchingIdentity HookProductBranchingRowDropIdentity
  constructor
  · intro h μ hμ
    rw [cornerRows_sum_comp_equiv μ (fun c : CornerCells μ => hookProductCornerRatio μ c)]
    exact h μ hμ
  · intro h μ hμ
    rw [← cornerRows_sum_comp_equiv μ (fun c : CornerCells μ => hookProductCornerRatio μ c)]
    exact h μ hμ

/-- The row-drop branching identity is equivalent to its explicit interval-product form. -/
theorem hookProductBranchingRowDropIdentity_iff_interval :
    HookProductBranchingRowDropIdentity ↔ HookProductBranchingRowDropIntervalIdentity := by
  unfold HookProductBranchingRowDropIdentity HookProductBranchingRowDropIntervalIdentity
  constructor
  · intro h μ hμ
    rw [← h μ hμ]
    apply Finset.sum_congr rfl
    intro r _hr
    exact (hookProductCornerRatio_eq_rowDropInterval μ r).symm
  · intro h μ hμ
    rw [← h μ hμ]
    apply Finset.sum_congr rfl
    intro r _hr
    exact hookProductCornerRatio_eq_rowDropInterval μ r

/--
If the hook-length formula already holds for a diagram, its tableau count can
be read as a rational factorial divided by the hook product.
-/
theorem standardTableauCount_eq_factorial_div_hookProduct_of_formula (ν : YoungDiagram)
    (hν : hookProduct ν * standardTableauCount ν = Nat.factorial ν.card) :
    (standardTableauCount ν : ℚ) =
      (Nat.factorial ν.card : ℚ) / (hookProduct ν : ℚ) := by
  have hprod : (hookProduct ν : ℚ) * (standardTableauCount ν : ℚ) =
      (Nat.factorial ν.card : ℚ) := by
    norm_num [← Nat.cast_mul, hν]
  have hhp : (hookProduct ν : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hookProduct_pos ν))
  field_simp [hhp] at hprod ⊢
  exact hprod

/-- The empty Young diagram has no cells in the local cell subtype. -/
theorem not_cell_bot (c : Cell (⊥ : YoungDiagram)) : False := by
  have hmem : c.val ∈ (∅ : Finset (ℕ × ℕ)) := by
    simpa only [YoungDiagram.cells_bot] using c.property
  cases hmem

/-- The empty hook product is the empty product. -/
@[simp]
theorem hookProduct_bot : hookProduct (⊥ : YoungDiagram) = 1 := by
  simp [hookProduct, YoungDiagram.cells_bot]

/-- There is exactly one standard tableau of empty shape. -/
@[simp]
theorem standardTableauCount_bot : standardTableauCount (⊥ : YoungDiagram) = 1 := by
  classical
  let T0 : Cell (⊥ : YoungDiagram) → Fin (⊥ : YoungDiagram).card :=
    fun c ↦ False.elim (not_cell_bot c)
  have hstd : IsStandardTableau (⊥ : YoungDiagram) T0 := by
    refine ⟨?_, ?_⟩
    · constructor
      · intro a
        exact False.elim (not_cell_bot a)
      · intro y
        have hy : y.val < 0 := by
          simpa [YoungDiagram.card, YoungDiagram.cells_bot] using y.isLt
        omega
    · intro a
      exact False.elim (not_cell_bot a)
  change Fintype.card
    {T : Cell (⊥ : YoungDiagram) → Fin (⊥ : YoungDiagram).card //
      IsStandardTableau (⊥ : YoungDiagram) T} = 1
  apply Fintype.card_eq_one_of_forall_eq (i := ⟨T0, hstd⟩)
  intro x
  apply Subtype.ext
  funext c
  exact False.elim (not_cell_bot c)

/-- The hook-length formula holds for the empty Young diagram. -/
theorem hookLengthFormula_bot :
    hookProduct (⊥ : YoungDiagram) * standardTableauCount (⊥ : YoungDiagram) =
      Nat.factorial (⊥ : YoungDiagram).card := by
  simp [YoungDiagram.card, YoungDiagram.cells_bot]

/-- Any Young diagram with no cells satisfies the hook-length formula. -/
theorem hookLengthFormula_empty_of_not_nonempty (μ : YoungDiagram)
    (hμ : ¬ μ.cells.Nonempty) :
    hookProduct μ * standardTableauCount μ = Nat.factorial μ.card := by
  have hbot : μ = (⊥ : YoungDiagram) := by
    apply YoungDiagram.ext
    have hcells : μ.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hμ
    simpa [YoungDiagram.cells_bot] using hcells
  subst μ
  exact hookLengthFormula_bot

/-- For a nonempty diagram, `card * (card - 1)! = card!` after casting to `ℚ`. -/
theorem factorial_pred_mul_card_eq_factorial_of_nonempty (μ : YoungDiagram)
    (hμ : μ.cells.Nonempty) :
    ((Nat.factorial (μ.card - 1) : ℕ) * μ.card : ℚ) =
      (Nat.factorial μ.card : ℚ) := by
  have hpos : 0 < μ.card := Finset.card_pos.mpr hμ
  have hsucc : μ.card = (μ.card - 1) + 1 := by omega
  rw [hsucc, Nat.factorial_succ]
  norm_num [Nat.cast_mul]
  ring

/-- A one-corner erasure has factorial cardinality `(μ.card - 1)!`. -/
theorem eraseCorner_factorial_eq_pred (μ : YoungDiagram) (c : CornerCells μ) :
    (Nat.factorial (eraseCorner μ c.1 c.2).card : ℚ) =
      (Nat.factorial (μ.card - 1) : ℚ) := by
  have hcard := eraseCorner_card_add_one μ c.1 c.2
  have h : (eraseCorner μ c.1 c.2).card = μ.card - 1 := by omega
  rw [h]

/-- Minimum hook-length formula target, stated without natural-number division. -/
def HookLengthFormulaStatement : Prop :=
  ∀ μ : YoungDiagram,
    hookProduct μ * standardTableauCount μ = Nat.factorial μ.card

/--
The named hook-product branching identity is sufficient to close the minimum
hook-length formula.
-/
theorem hookLengthFormula_of_hookProductBranchingIdentity
    (hbranch : HookProductBranchingIdentity) : HookLengthFormulaStatement := by
  classical
  intro μ
  generalize hn : μ.card = n
  revert μ
  refine Nat.strong_induction_on n ?_
  intro n IH μ hn
  subst n
  by_cases hμ : μ.cells.Nonempty
  · apply (Nat.cast_inj (R := ℚ)).mp
    let corners : Finset (CornerCells μ) :=
      @Finset.univ (CornerCells μ) inferInstance
    have hbranchμ :
        corners.sum (fun c => hookProductCornerRatio μ c) = (μ.card : ℚ) := by
      simpa [corners, HookProductBranchingIdentity] using hbranch μ hμ
    have htableau := standardTableauCount_eq_sum_erased μ hμ
    rw [Nat.cast_mul, htableau, Nat.cast_sum]
    calc
      (hookProduct μ : ℚ) *
          corners.sum (fun c => (standardTableauCount (eraseCorner μ c.1 c.2) : ℚ))
          = (hookProduct μ : ℚ) *
              corners.sum (fun c =>
                (Nat.factorial (eraseCorner μ c.1 c.2).card : ℚ) /
                  (hookProduct (eraseCorner μ c.1 c.2) : ℚ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro c _hc
            have hlt : (eraseCorner μ c.1 c.2).card < μ.card :=
              eraseCorner_card_lt μ c.1 c.2
            have hIH := IH (eraseCorner μ c.1 c.2).card hlt
              (eraseCorner μ c.1 c.2) rfl
            exact standardTableauCount_eq_factorial_div_hookProduct_of_formula
              (eraseCorner μ c.1 c.2) hIH
      _ = (hookProduct μ : ℚ) *
              corners.sum (fun c =>
                (Nat.factorial (μ.card - 1) : ℚ) /
                  (hookProduct (eraseCorner μ c.1 c.2) : ℚ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro c _hc
            rw [eraseCorner_factorial_eq_pred μ c]
      _ = (Nat.factorial (μ.card - 1) : ℚ) *
              corners.sum (fun c => hookProductCornerRatio μ c) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _hc
            rw [hookProductCornerRatio]
            field_simp [show (hookProduct (eraseCorner μ c.1 c.2) : ℚ) ≠ 0 by
              exact_mod_cast (Nat.ne_of_gt (hookProduct_pos (eraseCorner μ c.1 c.2)))]
      _ = (Nat.factorial (μ.card - 1) : ℚ) * (μ.card : ℚ) := by
            rw [hbranchμ]
      _ = (Nat.factorial μ.card : ℚ) := by
            simpa [Nat.cast_mul] using
              factorial_pred_mul_card_eq_factorial_of_nonempty μ hμ
  · exact hookLengthFormula_empty_of_not_nonempty μ hμ

/-- The content product route implies the hook-product branching identity. -/
theorem hookProductBranchingIdentity_of_content
    (hformula : HookProductRowDropContentProductFormula)
    (hcontent : HookProductBranchingContentIdentity) :
    HookProductBranchingIdentity := by
  have hinterval :=
    hookProductBranchingRowDropIntervalIdentity_of_content hformula hcontent
  exact hookProductBranchingIdentity_iff_rowDrops.mpr
    (hookProductBranchingRowDropIdentity_iff_interval.mpr hinterval)

/-- The content product route implies the public hook-length formula statement. -/
theorem hookLengthFormula_of_content
    (hformula : HookProductRowDropContentProductFormula)
    (hcontent : HookProductBranchingContentIdentity) :
    HookLengthFormulaStatement :=
  hookLengthFormula_of_hookProductBranchingIdentity
    (hookProductBranchingIdentity_of_content hformula hcontent)

/-- The hook-length formula for finite Young diagrams. -/
theorem hookLengthFormula : HookLengthFormulaStatement :=
  hookLengthFormula_of_content hookProductRowDropContentProductFormula
    hookProductBranchingContentIdentity

/--
Proof target alias retained for Atlas packet tooling and statement checks.
-/
def HookLengthFormulaTarget : Prop :=
  HookLengthFormulaStatement

/-- Checked target-shape sanity lemma. -/
theorem hookLengthFormulaTarget_iff :
    HookLengthFormulaTarget ↔ HookLengthFormulaStatement := by
  rfl

end AtlasKnownTheorems.HookLengthFormula
