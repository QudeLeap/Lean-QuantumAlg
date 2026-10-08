/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual selected-pivot GF(2) row elimination

The original statically selected pivot is skipped. Every other row reads
its current MSB-first pivot-column bit and conditionally executes the real
vector-row XOR instruction. Increasing target order is the original finite
sequence. This component does not choose a pivot or change its search policy.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The actual stored target row supplies the original logical-column test. -/
def eliminationBit (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (target : Fin rowCount) (column : Fin width) : CInputRef ctx .bit :=
  .wordBitGet (.vectorGet (.storage matrix.toCStorageRef) target) column

/-- One original closed instruction XORs the current pivot word into the current target word. -/
def eliminationXorOp (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) :
    ClassicalOp (.fixedVector rowCount (.unsignedWord width))
      (.fixedVector rowCount (.unsignedWord width)) ctx ctx :=
  .vectorRowXor rowCount width pivot target ctx (.storage matrix.toCStorageRef) matrix

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual selected stored bit decides whether the original row-XOR instruction executes. -/
def eliminationChoice (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (value : CShape.Value .bit) : Circuit model ctx ctx :=
  if value.toBool then
    BitWord.instruction (execution := model) (eliminationXorOp matrix pivot target)
  else .id ctx

/-- The pivot is statically skipped; every other row branches on its current real matrix bit. -/
def eliminateTarget (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) : Circuit model ctx ctx :=
  if target = pivot then .id ctx
  else .branch (eliminationBit matrix target column) (eliminationChoice matrix pivot target)

/-- The original increasing target order eliminates the selected column across the matrix. -/
def eliminateWithPivot (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) : Circuit model ctx ctx :=
  Circuit.forRange rowCount (fun target =>
    eliminateTarget (model := model) matrix pivot target column)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
