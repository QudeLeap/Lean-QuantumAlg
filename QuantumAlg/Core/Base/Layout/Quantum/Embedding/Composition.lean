/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Composition and multiplication of physical subsystem embeddings

These laws compare the complete operators of actual nested physical
embeddings. In particular, every unselected coordinate retains its identity
action. They introduce no circuit constructor or accounting annotation.
-/

namespace QuantumAlg.QuantumLayout.Embedding

noncomputable section

variable {small middle large : Nat}
  {source : QuantumLayout small} {intermediate : QuantumLayout middle}
  {target : QuantumLayout large}

/-- Compose two inclusions of the same physical wires. -/
public def compose (inner : QuantumLayout.Embedding source intermediate)
    (outer : QuantumLayout.Embedding intermediate target) :
    QuantumLayout.Embedding source target where
  position := inner.position.trans outer.position
  wire_eq index := (outer.wire_eq (inner.position index)).trans (inner.wire_eq index)

/-- Embeddings are determined by their actual position maps. -/
public lemma embedding_ext (first second : QuantumLayout.Embedding source target)
    (same : ∀ index, first.position index = second.position index) : first = second := by
  have positions : first.position = second.position := Function.Embedding.ext same
  cases first
  cases second
  cases positions
  rfl

private lemma complement_eq_iff (placement : QuantumLayout.Embedding source target)
    (row column : target.Basis) :
    (placement.splitBasis row).2 = (placement.splitBasis column).2 ↔
      ∀ position, position ∉ placement.selection → row position = column position := by
  constructor
  · intro same position absent
    exact congrFun same ⟨position, Finset.mem_compl.mpr absent⟩
  · intro same
    funext position
    exact same position.val (Finset.mem_compl.mp position.property)

private lemma selected_compose (inner : QuantumLayout.Embedding source intermediate)
    (outer : QuantumLayout.Embedding intermediate target) (basis : target.Basis) :
    ((compose inner outer).splitBasis basis).1 =
      (inner.splitBasis (outer.splitBasis basis).1).1 := by
  funext index
  apply Fin.ext
  rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value,
    QuantumLayout.Embedding.embedding_splitBasis_selected_value,
    QuantumLayout.Embedding.embedding_splitBasis_selected_value]
  rfl

private lemma complement_compose (inner : QuantumLayout.Embedding source intermediate)
    (outer : QuantumLayout.Embedding intermediate target) (row column : target.Basis) :
    ((compose inner outer).splitBasis row).2 =
        ((compose inner outer).splitBasis column).2 ↔
      (inner.splitBasis (outer.splitBasis row).1).2 =
          (inner.splitBasis (outer.splitBasis column).1).2 ∧
        (outer.splitBasis row).2 = (outer.splitBasis column).2 := by
  rw [complement_eq_iff, complement_eq_iff, complement_eq_iff]
  constructor
  · intro same
    constructor
    · intro position absent
      have absentOuter : outer.position position ∉ (compose inner outer).selection := by
        intro present
        obtain ⟨original, _, equality⟩ := Finset.mem_map.mp present
        have selected : inner.position original = position := outer.position.injective equality
        exact absent (selected ▸ Finset.mem_map_of_mem _ (Finset.mem_univ original))
      apply Fin.ext
      rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value,
        QuantumLayout.Embedding.embedding_splitBasis_selected_value]
      exact congrArg Fin.val (same (outer.position position) absentOuter)
    · intro position absent
      apply same
      intro present
      obtain ⟨original, _, equality⟩ := Finset.mem_map.mp present
      exact absent (equality ▸
        Finset.mem_map_of_mem outer.position (Finset.mem_univ (inner.position original)))
  · rintro ⟨innerSame, outerSame⟩ position absent
    by_cases selected : position ∈ outer.selection
    · obtain ⟨middlePosition, _, rfl⟩ := Finset.mem_map.mp selected
      have absentInner : middlePosition ∉ inner.selection := by
        intro present
        obtain ⟨original, _, equality⟩ := Finset.mem_map.mp present
        apply absent
        have same : (compose inner outer).position original = outer.position middlePosition :=
          congrArg outer.position equality
        exact same ▸ Finset.mem_map_of_mem _ (Finset.mem_univ original)
      have same := congrArg Fin.val (innerSame middlePosition absentInner)
      rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value,
        QuantumLayout.Embedding.embedding_splitBasis_selected_value] at same
      exact Fin.ext same
    · exact outerSame position selected

/-- Nested physical inclusions have exactly the same full operator as their composition. -/
public lemma embedding_lift_compose (inner : QuantumLayout.Embedding source intermediate)
    (outer : QuantumLayout.Embedding intermediate target)
    (operator : UnitaryOperator source.register) :
    outer.liftOperator (inner.liftOperator operator) =
      (compose inner outer).liftOperator operator := by
  apply Subtype.ext
  ext row column
  rw [QuantumLayout.Embedding.liftOperator_entry,
    QuantumLayout.Embedding.liftOperator_entry,
    QuantumLayout.Embedding.liftOperator_entry, selected_compose, selected_compose]
  have complements := complement_compose inner outer row column
  by_cases innerSame : (inner.splitBasis (outer.splitBasis row).1).2 =
      (inner.splitBasis (outer.splitBasis column).1).2
  · by_cases outerSame : (outer.splitBasis row).2 = (outer.splitBasis column).2
    · simp only [if_pos innerSame, if_pos outerSame,
        if_pos (complements.mpr ⟨innerSame, outerSame⟩), mul_one]
    · simp only [if_pos innerSame, if_neg outerSame,
        if_neg (fun same => outerSame (complements.mp same).2), mul_zero]
  · simp only [if_neg innerSame,
      if_neg (fun same => innerSame (complements.mp same).1), mul_zero, zero_mul]

/-- Physical extension preserves multiplication, including every spectator block. -/
public lemma embedding_lift_mul (placement : QuantumLayout.Embedding source target)
    (first second : UnitaryOperator source.register) :
    placement.liftOperator (first * second) =
      placement.liftOperator first * placement.liftOperator second := by
  apply Subtype.ext
  ext row column
  rw [QuantumLayout.Embedding.liftOperator_entry]
  let summand : target.Basis → ℂ := fun middle =>
    placement.liftOperator first row middle * placement.liftOperator second middle column
  change (∑ middle, first (placement.splitBasis row).1 middle *
      second middle (placement.splitBasis column).1) *
      (if (placement.splitBasis row).2 = (placement.splitBasis column).2 then 1 else 0) =
    ∑ middle, summand middle
  rw [← Equiv.sum_comp placement.splitBasis.symm summand, Fintype.sum_prod_type]
  simp only [summand, QuantumLayout.Embedding.liftOperator_entry, Equiv.apply_symm_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases same : (placement.splitBasis row).2 = (placement.splitBasis column).2
  · simp only [if_pos same]
    apply Finset.sum_congr
    · ext index
      simp only [Finset.mem_univ]
    · intro index _
      rfl
  · simp only [if_neg same, Finset.sum_const_zero]

end

end QuantumAlg.QuantumLayout.Embedding
