import QuantumOracle.Model.Database
import QuantumOracle.Model.LevelEmbedding
import Mathlib.Data.Fin.SuccPred

/-!
# Inserting a residual database with a prescribed input/output edge

Residual coordinates omit the selected input and output by `Fin.succAbove`.
The construction maps the actual edge graph and then adjoins the selected edge.
-/

noncomputable section

namespace QuantumOracle.ResidualDatabase

open scoped BigOperators

variable {N : ℕ}

/-- The coordinate inclusion omitting one selected input and output. -/
def edgeEmbedding (x y : Fin (N + 1)) :
    (Fin N × Fin N) ↪ (Fin (N + 1) × Fin (N + 1)) where
  toFun e := (x.succAbove e.1, y.succAbove e.2)
  inj' := by
    intro e f h
    exact Prod.ext (Fin.succAbove_right_injective (congrArg Prod.fst h))
      (Fin.succAbove_right_injective (congrArg Prod.snd h))

/-- Lift the residual edges without yet adding the prescribed edge. -/
def lift (x y : Fin (N + 1)) (I : Database N) : Database (N + 1) where
  edges := I.edges.map (edgeEmbedding x y)
  functional := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hf
    exact congrArg y.succAbove (I.functional ha hb (Fin.succAbove_right_injective h))
  injective := by
    intro e f he hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hf
    exact congrArg x.succAbove (I.injective ha hb (Fin.succAbove_right_injective h))

theorem mem_lift (x y : Fin (N + 1)) (I : Database N) (a b : Fin (N + 1)) :
    (a, b) ∈ (lift x y I).edges ↔
      ∃ u v, (u, v) ∈ I.edges ∧ x.succAbove u = a ∧ y.succAbove v = b := by
  simp only [lift, Finset.mem_map, edgeEmbedding, Function.Embedding.coeFn_mk,
    Prod.exists, Prod.mk.injEq]

@[simp] theorem mem_lift_succAbove (x y : Fin (N + 1)) (I : Database N) (a b : Fin N) :
    (x.succAbove a, y.succAbove b) ∈ (lift x y I).edges ↔ (a, b) ∈ I.edges := by
  rw [mem_lift]
  simp only [Fin.succAbove_right_inj]
  constructor
  · rintro ⟨u, v, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

theorem input_fresh (x y : Fin (N + 1)) (I : Database N) : x ∉ (lift x y I).domain := by
  intro h
  obtain ⟨b, hb⟩ := (Database.mem_domain _ _).mp h
  obtain ⟨u, v, _, hu, _⟩ := (mem_lift x y I x b).mp hb
  exact Fin.succAbove_ne x u hu

theorem output_fresh (x y : Fin (N + 1)) (I : Database N) : y ∉ (lift x y I).image := by
  intro h
  obtain ⟨a, ha⟩ := (Database.mem_image _ _).mp h
  obtain ⟨u, v, _, _, hv⟩ := (mem_lift x y I a y).mp ha
  exact Fin.succAbove_ne y v hv

@[simp] theorem lift_size (x y : Fin (N + 1)) (I : Database N) :
    (lift x y I).size = I.size := by
  rw [Database.size_eq_card_edges, Database.size_eq_card_edges]
  exact Finset.card_map _

/-- Insert the prescribed edge into the lifted residual database. -/
def insert (x y : Fin (N + 1)) (I : Database N) : Database (N + 1) :=
  (lift x y I).set x y

theorem insert_edges (x y : Fin (N + 1)) (I : Database N) :
    (insert x y I).edges = Insert.insert (x, y) ((lift x y I).edges) :=
  Database.set_edges_of_fresh _ x y (input_fresh x y I) (output_fresh x y I)

theorem mem_insert (x y : Fin (N + 1)) (I : Database N) (a b : Fin (N + 1)) :
    (a, b) ∈ (insert x y I).edges ↔
      (a = x ∧ b = y) ∨
        ∃ u v, (u, v) ∈ I.edges ∧ x.succAbove u = a ∧ y.succAbove v = b := by
  rw [insert_edges, Finset.mem_insert, Prod.mk.injEq, mem_lift]

@[simp] theorem insert_contains (x y : Fin (N + 1)) (I : Database N) :
    (x, y) ∈ (insert x y I).edges := Database.set_contains _ _ _

@[simp] theorem mem_insert_succAbove (x y : Fin (N + 1)) (I : Database N) (a b : Fin N) :
    (x.succAbove a, y.succAbove b) ∈ (insert x y I).edges ↔ (a, b) ∈ I.edges := by
  rw [insert_edges, Finset.mem_insert, Prod.mk.injEq, mem_lift_succAbove]
  simp only [Fin.succAbove_ne, false_and, false_or]

@[simp] theorem insert_size (x y : Fin (N + 1)) (I : Database N) :
    (insert x y I).size = I.size + 1 := by
  rw [insert, Database.set_size_of_fresh _ _ _ (input_fresh x y I) (output_fresh x y I),
    lift_size]

theorem insert_injective (x y : Fin (N + 1)) : Function.Injective (insert x y) := by
  intro I J h
  apply Database.ext
  ext ⟨a, b⟩
  rw [← mem_insert_succAbove x y I a b, ← mem_insert_succAbove x y J a b, h]

theorem insert_ne_of_ne (x : Fin (N + 1)) {y z : Fin (N + 1)} (hyz : y ≠ z)
    (I J : Database N) : insert x y I ≠ insert x z J := by
  intro h
  have hy := insert_contains x y I
  rw [h] at hy
  exact hyz ((insert x z J).functional hy (insert_contains x z J) rfl)

theorem disjoint_ranges (x : Fin (N + 1)) {y z : Fin (N + 1)} (hyz : y ≠ z) :
    Disjoint (Set.range (insert x y)) (Set.range (insert x z)) := by
  apply Set.disjoint_left.mpr
  rintro K ⟨I, rfl⟩ ⟨J, hJ⟩
  exact insert_ne_of_ne x hyz I J hJ.symm

/-- Jointly insert the answer and residual database at the selected input. -/
def jointInsert (x : Fin (N + 1)) (p : Fin (N + 1) × Database N) : Database (N + 1) :=
  insert x p.1 p.2

theorem jointInsert_injective (x : Fin (N + 1)) : Function.Injective (jointInsert x) := by
  rintro ⟨y, I⟩ ⟨z, J⟩ h
  change insert x y I = insert x z J at h
  have hyz : y = z := by
    by_contra hne
    exact insert_ne_of_ne x hne I J h
  subst z
  exact Prod.ext rfl (insert_injective x y h)

def jointRangeEquiv (x : Fin (N + 1)) :
    (Fin (N + 1) × Database N) ≃ Set.range (jointInsert x) :=
  Equiv.ofInjective _ (jointInsert_injective x)

private def zeroPad {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) :
    EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ B := by
  classical
  letI : Fintype (Set.range f) := Subtype.fintype (fun b : B => b ∈ Set.range f)
  let e := Equiv.ofInjective f hf
  exact
    { toFun := fun v => WithLp.toLp 2 (fun K =>
        if hK : K ∈ Set.range f then v (e.symm ⟨K, hK⟩) else 0)
      map_add' := by
        intro v w
        ext K
        simp only [PiLp.toLp_apply, PiLp.add_apply]
        by_cases hK : K ∈ Set.range f <;>
          simp only [hK, dite_true, dite_false, add_zero]
      map_smul' := by
        intro c v
        ext K
        simp only [PiLp.toLp_apply, PiLp.smul_apply, RingHom.id_apply]
        by_cases hK : K ∈ Set.range f <;>
          simp only [hK, dite_true, dite_false, smul_zero]
      norm_map' := by
        intro v
        change ‖WithLp.toLp 2 (fun K =>
          if hK : K ∈ Set.range f then v (e.symm ⟨K, hK⟩) else 0)‖ = ‖v‖
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        simp only [PiLp.toLp_apply]
        rw [← Fintype.sum_subtype_add_sum_subtype (fun K : B => K ∈ Set.range f)]
        have hpos : (∑ K : Set.range f,
            ‖(if hK : K.val ∈ Set.range f then v (e.symm ⟨K.val, hK⟩) else 0)‖ ^ 2) =
            ∑ p : A, ‖v p‖ ^ 2 := by
          calc
            _ = ∑ K : Set.range f, ‖v (e.symm K)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro K _
              simp only [K.property, dite_true]
            _ = _ := e.symm.sum_comp (fun p => ‖v p‖ ^ 2)
        have hneg : (∑ K : {K : B // K ∉ Set.range f},
            ‖(if hK : K.val ∈ Set.range f then v (e.symm ⟨K.val, hK⟩) else 0)‖ ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro K _
          simp only [K.property, dite_false, norm_zero, zero_pow, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true]
        exact (congrArg₂ (· + ·) hpos hneg).trans (add_zero _) }

private theorem zeroPad_apply {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (v : EuclideanSpace ℂ A) (a : A) :
    zeroPad f hf v (f a) = v a := by
  classical
  have h : f a ∈ Set.range f := ⟨a, rfl⟩
  change (if hb : f a ∈ Set.range f then
    v ((Equiv.ofInjective f hf).symm ⟨f a, hb⟩) else 0) = _
  rw [dif_pos h]
  exact congrArg v (Equiv.ofInjective_symm_apply hf a)

private theorem zeroPad_apply_of_notMem {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (v : EuclideanSpace ℂ A) (b : B)
    (hb : b ∉ Set.range f) : zeroPad f hf v b = 0 := by
  classical
  change (if h : b ∈ Set.range f then
    v ((Equiv.ofInjective f hf).symm ⟨b, h⟩) else 0) = _
  exact dif_neg hb

attribute [local irreducible] zeroPad

/-- Actual zero padding of the answer and residual-database register into the
full database register, along the concrete insertion of edge graphs. -/
def jointIota (x : Fin (N + 1)) :
    EuclideanSpace ℂ (Fin (N + 1) × Database N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Database (N + 1)) :=
  zeroPad (jointInsert x) (jointInsert_injective x)

@[simp] theorem jointIota_apply_insert (x : Fin (N + 1))
    (v : EuclideanSpace ℂ (Fin (N + 1) × Database N)) (y : Fin (N + 1)) (I : Database N) :
    jointIota x v (insert x y I) = v (y, I) :=
  zeroPad_apply _ (jointInsert_injective x) v (y, I)

@[simp] theorem jointIota_apply_of_notMem (x : Fin (N + 1))
    (v : EuclideanSpace ℂ (Fin (N + 1) × Database N)) (K : Database (N + 1))
    (hK : K ∉ Set.range (jointInsert x)) : jointIota x v K = 0 :=
  zeroPad_apply_of_notMem _ (jointInsert_injective x) v K hK

end QuantumOracle.ResidualDatabase
