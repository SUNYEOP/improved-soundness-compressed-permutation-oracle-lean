import QuantumOracle.Proof.SpechtFoundation
import QuantumOracle.Proof.HookLengthFormula

/-!
# Concrete hook and tableau-count compatibility

The two independently formalized hook statistics agree on every actual cell.
Their products therefore agree, and the exact multiplicative hook identities
identify the two actual tableau counts. In particular, the actual Specht
module's dimension is the actual ProofAtlas standard-tableau count.

No identification with a QuantumOracle harmonic layer or Gram eigenspace is
asserted, and no particular equivalence of tableau types is selected.
-/

noncomputable section

namespace QuantumOracle.SpechtHookBridge

open scoped BigOperators

theorem hookLength_eq_proofAtlas (mu : YoungDiagram)
    (c : AtlasKnownTheorems.HookLengthFormula.Cell mu) :
    SpechtFoundation.hookLength mu c.val.1 c.val.2 =
      AtlasKnownTheorems.HookLengthFormula.hookLength mu c := by
  rw [SpechtFoundation.hookLength_eq,
    AtlasKnownTheorems.HookLengthFormula.hookLength_eq_rowLen_sub_add_colLen_sub_sub_one]
  have hrow : c.val.2 < mu.rowLen c.val.1 := by
    simpa using (YoungDiagram.mem_iff_lt_rowLen (μ := mu)
      (i := c.val.1) (j := c.val.2)).mp c.property
  have hcol : c.val.1 < mu.colLen c.val.2 := by
    simpa using (YoungDiagram.mem_iff_lt_colLen (μ := mu)
      (i := c.val.1) (j := c.val.2)).mp c.property
  omega

theorem hookProduct_eq_proofAtlas (mu : YoungDiagram) :
    SpechtFoundation.hookProduct mu =
      AtlasKnownTheorems.HookLengthFormula.hookProduct mu := by
  rw [SpechtFoundation.hookProduct_eq_prod,
    AtlasKnownTheorems.HookLengthFormula.hookProduct]
  rw [← Finset.prod_attach mu.cells]
  apply Finset.prod_congr rfl
  intro c _
  exact hookLength_eq_proofAtlas mu c

theorem diagram_card {N : ℕ} (la : Nat.Partition N) :
    (SpechtFoundation.diagram la).card = N :=
  RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.card_toYoungDiagram_cells la

/-- Equality of actual counts follows from the two exact hook identities and
positivity of their common hook product. -/
theorem tableauCount_eq_proofAtlas (N : ℕ) (la : Nat.Partition N) :
    SpechtFoundation.tableauCount N la =
      AtlasKnownTheorems.HookLengthFormula.standardTableauCount (SpechtFoundation.diagram la) := by
  have hs := SpechtFoundation.tableauCount_mul_hookProduct N la
  have ha := AtlasKnownTheorems.HookLengthFormula.hookLengthFormula (SpechtFoundation.diagram la)
  rw [← hookProduct_eq_proofAtlas, diagram_card] at ha
  apply mul_left_cancel₀ (ne_of_gt (SpechtFoundation.hookProduct_pos (SpechtFoundation.diagram la)))
  calc
    SpechtFoundation.hookProduct (SpechtFoundation.diagram la) *
        SpechtFoundation.tableauCount N la = N.factorial := by simpa only [mul_comm] using hs
    _ = _ := ha.symm

/-- The constructed Specht ideal has the ProofAtlas standard-tableau count
as its actual complex dimension. -/
theorem dimension_eq_proofAtlas_tableauCount (N : ℕ) (la : Nat.Partition N) :
    Module.finrank ℂ (SpechtFoundation.specht N la) =
      AtlasKnownTheorems.HookLengthFormula.standardTableauCount (SpechtFoundation.diagram la) := by
  rw [SpechtFoundation.dimension_eq_tableauCount, tableauCount_eq_proofAtlas]

end QuantumOracle.SpechtHookBridge
