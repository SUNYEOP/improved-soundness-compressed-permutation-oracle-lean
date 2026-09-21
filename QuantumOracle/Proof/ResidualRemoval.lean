import QuantumOracle.Proof.ResidualDatabase

/-!
# Actual residual removal of a prescribed edge

The residual database pulls the actual graph back along the two `succAbove`
coordinate inclusions. If the removed edge is present, insertion and removal
are inverse and the database size decreases by exactly one.
-/

namespace QuantumOracle.ResidualRemoval

variable {N : ℕ}

/-- Remove the selected input and output from an actual database graph. Edges
incident to either omitted coordinate are excluded by the pullback. -/
def remove (x y : Fin (N + 1)) (I : Database (N + 1)) : Database N where
  edges := Finset.univ.filter (fun e => (x.succAbove e.1, y.succAbove e.2) ∈ I.edges)
  functional := by
    intro e f he hf h
    exact Fin.succAbove_right_injective
      (I.functional (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
        (congrArg x.succAbove h))
  injective := by
    intro e f he hf h
    exact Fin.succAbove_right_injective
      (I.injective (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
        (congrArg y.succAbove h))

@[simp] theorem mem_remove (x y : Fin (N + 1)) (I : Database (N + 1)) (a b : Fin N) :
    (a, b) ∈ (remove x y I).edges ↔ (x.succAbove a, y.succAbove b) ∈ I.edges := by
  simp only [remove, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem remove_insert (x y : Fin (N + 1)) (I : Database N) :
    remove x y (ResidualDatabase.insert x y I) = I := by
  apply Database.ext
  ext ⟨a, b⟩
  rw [mem_remove, ResidualDatabase.mem_insert_succAbove]

/-- A database containing the prescribed edge is exactly the insertion of its
actual residual pullback. -/
theorem insert_remove (x y : Fin (N + 1)) (I : Database (N + 1))
    (hxy : (x, y) ∈ I.edges) : ResidualDatabase.insert x y (remove x y I) = I := by
  apply Database.ext
  ext ⟨a, b⟩
  rw [ResidualDatabase.mem_insert]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨u, v, huv, rfl, rfl⟩)
    · exact hxy
    · exact (mem_remove x y I u v).mp huv
  · intro hab
    by_cases ha : a = x
    · exact Or.inl ⟨ha, I.functional hab hxy ha⟩
    · have hb : b ≠ y := fun hb => ha (I.injective hab hxy hb)
      obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq ha
      obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq hb
      exact Or.inr ⟨u, v, (mem_remove x y I u v).mpr hab, rfl, rfl⟩

theorem size_remove_add_one (x y : Fin (N + 1)) (I : Database (N + 1))
    (hxy : (x, y) ∈ I.edges) : (remove x y I).size + 1 = I.size := by
  have h := congrArg Database.size (insert_remove x y I hxy)
  simpa only [ResidualDatabase.insert_size] using h

theorem size_remove (x y : Fin (N + 1)) (I : Database (N + 1))
    (hxy : (x, y) ∈ I.edges) : (remove x y I).size = I.size - 1 := by
  have h := size_remove_add_one x y I hxy
  omega

theorem lift_remove_edges_subset (x y : Fin (N + 1)) (I : Database (N + 1)) :
    (ResidualDatabase.lift x y (remove x y I)).edges ⊆ I.edges := by
  rintro ⟨a, b⟩ hab
  obtain ⟨u, v, huv, rfl, rfl⟩ := (ResidualDatabase.mem_lift x y (remove x y I) a b).mp hab
  exact (mem_remove x y I u v).mp huv

theorem size_remove_le (x y : Fin (N + 1)) (I : Database (N + 1)) :
    (remove x y I).size ≤ I.size := by
  rw [← ResidualDatabase.lift_size x y (remove x y I),
    Database.size_eq_card_edges, Database.size_eq_card_edges]
  exact Finset.card_le_card (lift_remove_edges_subset x y I)

/-- The joint insertion image is exactly the databases that define the selected input. -/
theorem mem_range_jointInsert_iff (x : Fin (N + 1)) (I : Database (N + 1)) :
    I ∈ Set.range (ResidualDatabase.jointInsert x) ↔ x ∈ I.domain := by
  constructor
  · rintro ⟨⟨y, J⟩, rfl⟩
    exact (Database.mem_domain _ _).mpr ⟨y, ResidualDatabase.insert_contains x y J⟩
  · intro hx
    obtain ⟨y, hxy⟩ := (Database.mem_domain I x).mp hx
    exact ⟨(y, remove x y I), insert_remove x y I hxy⟩

end QuantumOracle.ResidualRemoval
