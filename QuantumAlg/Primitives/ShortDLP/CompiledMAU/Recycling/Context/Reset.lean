/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context.Coordinates
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ControlKraus
import all QuantumAlg.Components.Encoded.StateEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual measured-reset row on the context's clean carrier

The reset row is the operator already
derived from the actual measured reset in Stage. Its outcome is cast to the
actual selected wire through its proved dimension equality. The rectangular
equation is proved on all physical rows, including rows outside the clean
carrier, and all reference entries. No caller-supplied channel equation is used.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.ContextReset

noncomputable section

open Execution
open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- The reset row reaches exactly the control-zero encoding of the same source seed/reference. -/
private lemma resetCondition (Reference : Register) (outcome : Fin 2)
    (row : ((Context base noQuantum m ell width).register.prod Reference).Index)
    (column : ((Carrier.full modulus.val).prod Reference).Index) :
    (row.1 (control base noQuantum m ell width) = 0 ∧
      (Placement.embedding base noQuantum m ell width modulus positive column.1, column.2) =
        (Function.update row.1 (control base noQuantum m ell width)
          (ContextCoordinates.physicalBit base noQuantum m ell width outcome), row.2)) ↔
    (column.1.1 = outcome ∧
      (Placement.embedding base noQuantum m ell width modulus positive (0, column.1.2),
        column.2) = row) := by
  let e := Placement.embedding base noQuantum m ell width modulus positive
  let wire := control base noQuantum m ell width
  let bit := ContextCoordinates.physicalBit base noQuantum m ell width
  constructor
  · rintro ⟨zero, written⟩
    have registers : e column.1 = Function.update row.1 wire (bit outcome) :=
      congrArg Prod.fst written
    have selected := congrArg (fun basis => basis wire) registers
    rw [ContextCoordinates.embedding_control, Function.update_self] at selected
    have outcomeSame : column.1.1 = outcome :=
      ContextCoordinates.physicalBit_injective base noQuantum m ell width selected
    have rowUnchanged : Function.update row.1 wire 0 = row.1 := by
      rw [← zero]
      exact Function.update_eq_self wire row.1
    have resetBack := congrArg (fun basis => Function.update basis wire (bit 0)) registers
    have bitZero : bit 0 = 0 := ContextCoordinates.physicalBit_zero base noQuantum m ell width
    rw [ContextCoordinates.embedding_update, bitZero,
      Function.update_idem, rowUnchanged] at resetBack
    have referenceSame : column.2 = row.2 :=
      congrArg (fun pair : ((Context base noQuantum m ell width).register.prod Reference).Index =>
        pair.2) written
    exact ⟨outcomeSame, Prod.ext resetBack referenceSame⟩
  · rintro ⟨outcomeSame, encoded⟩
    rw [← encoded]
    constructor
    · exact (ContextCoordinates.embedding_control base noQuantum m ell width modulus positive
        (0, column.1.2)).trans (ContextCoordinates.physicalBit_zero base noQuantum m ell width)
    · rw [ContextCoordinates.embedding_update]
      exact Prod.ext (congrArg e (Prod.ext outcomeSame rfl)) rfl

/-- Full reset intertwiner, with no restriction on the physical row or reference coherence. -/
lemma resetRow_intertwines (Reference : Register) (outcome : Fin 2) :
    let native : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
      resetRow base noQuantum m ell width Reference
        (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
    let j : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix (BasisEmbedding.withReference
        (Placement.embedding base noQuantum m ell width modulus positive) Reference)
    let source : Matrix ((Carrier.full modulus.val).prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      ControlKraus.resetBlock (S := Carrier.units modulus.val) outcome ⊗ₖ
        (1 : HilbertOperator Reference)
    native * j = j * source := by
  let n : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    resetRow base noQuantum m ell width Reference
      (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
  let j : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (Placement.embedding base noQuantum m ell width modulus positive) Reference)
  let s : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    ControlKraus.resetBlock (S := Carrier.units modulus.val) outcome ⊗ₖ
      (1 : HilbertOperator Reference)
  have sourceEntry
      (index column : (Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) :
      s index column =
        if index = ((0, column.1.2), column.2) then
          if column.1.1 = outcome then 1 else 0 else 0 := by
    rcases index with ⟨⟨indexBit, indexSeed⟩, indexRef⟩
    rcases column with ⟨⟨columnBit, columnSeed⟩, columnRef⟩
    simp only [s, Matrix.kronecker_apply, ControlKraus.resetBlock, Matrix.one_apply]
    by_cases bit : indexBit = 0 <;>
      by_cases selected : columnBit = outcome <;>
      by_cases seed : indexSeed = columnSeed <;>
      by_cases reference : indexRef = columnRef <;>
      simp [bit, selected, seed, reference, Prod.mk.injEq]
  change n * j = j * s
  ext row column
  simp only [Matrix.mul_apply, sourceEntry, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq']
  simp only [j, BasisEmbedding.matrix, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (if row.1 (control base noQuantum m ell width) = 0 ∧
      (Placement.embedding base noQuantum m ell width modulus positive column.1, column.2) =
        (Function.update row.1 (control base noQuantum m ell width)
          (ContextCoordinates.physicalBit base noQuantum m ell width outcome), row.2)
      then (1 : ℂ) else 0) = _
  have law := resetCondition base noQuantum m ell width modulus positive Reference outcome
    row column
  by_cases selected : column.1.1 = outcome
  · rw [if_pos selected]
    by_cases encoded :
        (Placement.embedding base noQuantum m ell width modulus positive (0, column.1.2),
          column.2) = row
    · exact (if_pos (law.mpr ⟨selected, encoded⟩)).trans (if_pos encoded).symm
    · exact (if_neg (fun found => encoded (law.mp found).2)).trans (if_neg encoded).symm
  · exact (if_neg (fun found => selected (law.mp found).1)).trans (if_neg selected).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.ContextReset
