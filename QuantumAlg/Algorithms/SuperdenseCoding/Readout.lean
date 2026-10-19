/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Matrix
import all QuantumAlg.Algorithms.SuperdenseCoding.Matrix
import all QuantumAlg.Algorithms.SuperdenseCoding.Geometry
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Reading the actual superdense-coding measurement results

The output's finite values are the ones written by the Z instructions on the
source-defined decoded basis. The source bit pairs are used to state this
relation, never as a replacement for a measurement result
[dW19, qcnotes.tex:885-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

/-- Independent finite encoding of the classical message promised at the input. -/
public def messageValue {count : Nat} (bits : SuperdenseMessage count) :
    CShape.Value (messageShape count) :=
  .fixedVector fun index => .product
    (.finite (binaryBit (bits index).1)) (.finite (binaryBit (bits index).2))

/-- Structural selection of the stored finite source message recovers its Boolean labels. -/
lemma storedBits_messageValue {count : Nat} (bits : SuperdenseMessage count) :
    storedBits (messageValue bits) = bits := by
  funext index
  change (decide ((binaryBit (bits index).1).val = 1),
    decide ((binaryBit (bits index).2).val = 1)) = bits index
  rcases bits index with ⟨first, second⟩
  cases first <;> cases second <;> rfl

private lemma wireIndex_castSucc {count : Nat} (block : Fin count) (side : Fin 2) :
    wireIndex block.castSucc side = Fin.castAdd 2 (wireIndex block side) := by
  apply Fin.ext
  rfl

private lemma wireIndex_last (count : Nat) (side : Fin 2) :
    wireIndex (Fin.last count) side = Fin.natAdd (width count) side := by
  apply Fin.ext
  change side.val + 2 * count = width count + side.val
  rw [width_eq]
  omega

private lemma blockBasis_coordinate (first second : Bool) (side : Fin 2) :
    (QuantumSignature.qubitsIndexEquiv 2).symm (blockBasis first second) side =
      binaryBit (if side.val = 0 then second else first) := by
  fin_cases side <;> cases first <;> cases second <;> rfl

/-- Each source block occupies its own two physical positions in the joint decoded basis. -/
lemma decodedBasis_coordinate (count : Nat) (bits : SuperdenseMessage count)
    (block : Fin count) (side : Fin 2) :
    (QuantumSignature.qubitsIndexEquiv (width count)).symm (decodedBasis count bits)
        (wireIndex block side) =
      binaryBit (if side.val = 0 then (bits block).2 else (bits block).1) := by
  induction count with
  | zero => exact Fin.elim0 block
  | succ count ih =>
      refine Fin.lastCases ?_ (fun previous => ?_) block
      · rw [wireIndex_last, decodedBasis]
        exact (BinaryBasis.bigEndianEquiv_prod_right _ _ side).trans
          (blockBasis_coordinate _ _ side)
      · rw [wireIndex_castSucc, decodedBasis]
        exact (BinaryBasis.bigEndianEquiv_prod_left _ _ (wireIndex previous side)).trans
          (ih (fun index => bits index.castSucc) previous)

/-- Complete context transport preserves each original physical decoded bit. -/
lemma finalBasis_coordinate (count : Nat) (bits : SuperdenseMessage count)
    (block : Fin count) (side : Fin 2) :
    (finalBasis count bits (position count (wireIndex block side))).val =
      (binaryBit (if side.val = 0 then (bits block).2 else (bits block).1)).val := by
  change (basisOfEqualWires _ _ (context_wires count)
    ((QuantumSignature.qubitsIndexEquiv (width count)).symm (decodedBasis count bits))
      (positionsOfEqualWires _ _ (context_wires count) (wireIndex block side))).val = _
  rw [basisOfEqualWires_value, decodedBasis_coordinate]

private lemma finite_value_eq (value : CShape.Value (.finite 2)) (expected : Fin 2)
    (equal : value.toFin.val = expected.val) : value = .finite expected := by
  cases value with
  | finite value => exact congrArg CShape.Value.finite (Fin.ext equal)

/-- Every actual result write contains the corresponding bit of the decoded joint state. -/
lemma written_result_cell (count : Nat) (bits : SuperdenseMessage count)
    (store : Store (context count)) (block : Fin count) (side : Fin 2) :
    (Circuit.writeMeasurementPath (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts count) store
      (Circuit.measurementBasisPath (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count) (finalBasis count bits))).read
          (.storage (resultCell count (wireIndex block side)).toCStorageRef) =
      .finite (binaryBit (if side.val = 0 then (bits block).2 else (bits block).1)) := by
  apply finite_value_eq
  exact (QubitReadouts.written_value (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (services := .empty)
    (position count) (position_dimension count) (resultCell count)
    (MeasurementCells.reference_key_injective (inputContext count) 2 (width count))
    store (finalBasis count bits) (wireIndex block side)).trans
      (finalBasis_coordinate count bits block side)

/-- Reading the actual stored outcomes yields the entire original message. -/
public lemma superdense_written_output (count : Nat) (bits : SuperdenseMessage count)
    (store : Store (context count)) :
    (Circuit.writeMeasurementPath (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts count) store
      (Circuit.measurementBasisPath (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count) (finalBasis count bits))).read (resultInput count) =
      messageValue bits := by
  change CShape.Value.fixedVector _ = CShape.Value.fixedVector _
  apply congrArg CShape.Value.fixedVector
  funext block
  change CShape.Value.product _ _ = CShape.Value.product _ _
  rw [written_result_cell, written_result_cell]
  rfl

end
end QuantumAlg.SuperdenseCoding.Execution
