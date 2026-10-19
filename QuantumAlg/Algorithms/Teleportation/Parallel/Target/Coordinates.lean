/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Target
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource.Insertion

/-!
# Independent teleportation target in the original physical coordinates

These mathematical coordinate equalities retain Alice's two measured systems,
Bob's original output system, and every external-reference matrix entry.
They impose no input-state condition and do not define a new execution.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.Target

noncomputable section

open Execution NativeCoordinates PhysicalNative

private lemma native_output_parts (label : Fin 8) :
    (prodEquiv (m := 2) (n := 1)).symm label =
      ((finProdFinEquiv (m := 2) (n := 2))
        ((BinaryBasis.bigEndianEquiv 3).symm label 0,
         (BinaryBasis.bigEndianEquiv 3).symm label 1),
        (BinaryBasis.bigEndianEquiv 3).symm label 2) := by
  fin_cases label <;> decide

/-- The target places measured Alice labels and Bob's input on their original physical wires. -/
lemma outputBasis_native (count : Nat) (labels : Fin count → Fin 8) :
    outputBasis count ((contextBankBasis count).symm labels) =
      ((fun block => ((prodEquiv (m := 2) (n := 1)).symm (labels block)).1),
       (fun block => ((prodEquiv (m := 2) (n := 1)).symm (labels block)).2)) := by
  let physical := basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)
  let decoded := (BinaryBasis.bigEndianEquiv (width count)).symm
    ((bankBinaryBasis count).symm labels)
  have transported : physical.symm ((contextBankBasis count).symm labels) = decoded :=
    physical.symm_apply_apply decoded
  refine (congrArg (fun basis : (layout count).register.Index =>
    outputBank count (tripleBasis count basis)) transported).trans ?_
  apply Prod.ext
  · funext block
    change (finProdFinEquiv (m := 2) (n := 2))
      (tripleBasis count decoded block 0, tripleBasis count decoded block 1) = _
    rw [tripleBasis_native_decode]
    exact (congrArg Prod.fst (native_output_parts (labels block))).symm
  · funext block
    change tripleBasis count decoded block 2 = _
    rw [tripleBasis_native_decode]
    exact (congrArg Prod.snd (native_output_parts (labels block))).symm

/-- Tracing only the original Bell resource retains every input/reference matrix entry. -/
lemma originalInput_entry (count : Nat) {Reference : Register}
    (input : Input (context count) Reference)
    (row column : (inputRegister count).Index) (leftRef rightRef : Reference.Index) :
    (originalInput count input).matrix (row, leftRef) (column, rightRef) =
      BellInsertion.inputReferenceSlice count input.state.quantumMarginal leftRef rightRef
        row column := by
  rw [originalInput, DensityOperator.marginalLeft_matrix]
  simp only [DensityOperator.reindex_entry]
  rfl

end

end QuantumAlg.QuantumTeleportation.Parallel.Target
