/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.ResetMeasurement
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Gates.Hadamard.Layer.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix

/-!
# Actual numerator Hadamard, Z writes, and stored-result X reset

The original numerator receives the existing Hadamard layer. Its Z
outcomes are written to the actual finite result cells, whose structural
read selects the literal X reset sequence. The finite label below only
indexes this compiled gate family; no packed word is allocated or written.
Every numerator, input and EEA history wire remains live throughout
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorReset

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- A stored finite vector indexes its concrete literal X sequence in little-endian order. -/
def outcome {width : Nat} (value : CShape.Value (.fixedVector width (.finite 2))) :
    Fin (2 ^ width) :=
  ⟨Nat.ofBits (QubitReadouts.mask value), Nat.ofBits_lt_two_pow _⟩

theorem outcome_bit {width : Nat} (value : CShape.Value (.fixedVector width (.finite 2)))
    (index : Fin width) :
    (outcome value).val.testBit index.val = QubitReadouts.mask value index := by
  exact Nat.testBit_ofBits_lt (QubitReadouts.mask value) index.val index.isLt

/-- The chosen literal reset uses only the existing numerator after the complete source frame. -/
def member (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2))) :
    UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width) :=
  UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
    (StoredWordReset.program (QubitLayout.canonical width) (outcome value))

/-- The same selected native sequence resets Y and preserves the entire remaining source label. -/
theorem member_ket (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2)))
    (frame : Fin (2 ^ (encoding width).width)) :
    (member width value).binaryMatrix.apply
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (frame, outcome value))) =
      NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (frame, 0)) := by
  rw [member]
  change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
      (StoredWordReset.program (QubitLayout.canonical width) (outcome value))).binaryMatrix.apply
        (NormalizedVector.ket (R := Qubits ((encoding width).width + width))
          (prodEquiv (frame, outcome value))) =
      NormalizedVector.ket (R := Qubits ((encoding width).width + width))
        (prodEquiv (frame, 0))
  rw [UnitaryCircuit.onCanonicalBinarySuffix_binaryMatrix,
    ← NormalizedVector.tensor_ket, UnitaryOperator.tensor_apply_tensor,
    UnitaryOperator.one_apply]
  change (NormalizedVector.ket frame).tensor
    ((StoredWordReset.binaryProgram (outcome value)).apply
      (NormalizedVector.ket (outcome value))) = _
  rw [StoredWordReset.storedWordReset_binary_ket, NormalizedVector.tensor_ket]

/-- Read the actual finite outcomes and execute precisely their selected X sequence. -/
def reset (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context width)
      (NumeratorMeasurement.context width) :=
  NumeratorRuntime.selected width (member width)

/-- The native Hadamard layer acts only on the original numerator word. -/
def hadamardMember (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width) :=
  UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
    (Gate.HadamardLayer.circuit .empty width)

/-- Execute that same Hadamard layer in the actual shared runtime context. -/
def hadamard (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context width)
      (NumeratorMeasurement.context width) :=
  NumeratorRuntime.code width (hadamardMember width)

/-- Actual H gates, actual Z writes, then a branch reading those same stored finite results. -/
def code (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context width)
      (NumeratorMeasurement.context width) :=
  .seq (hadamard width) (.seq (NumeratorMeasurement.measure width) (reset width))

/-- Each selected reset charges exactly its concrete X gate multiplicity. -/
theorem reset_cost (width : Nat) (path : (reset width).Path) :
    (reset width).resourcePool path =
      EncodedBit.Word.BasisLoad.xCount (outcome path.1) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit) := by
  change ResourcePool.ofList (NumeratorRuntime.program width (member width path.1)).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]
  change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
    (StoredWordReset.program (QubitLayout.canonical width) (outcome path.1))).eventCost = _
  exact (UnitaryCircuit.onCanonicalBinarySuffix_eventCost (encoding width).width
    (StoredWordReset.program (QubitLayout.canonical width) (outcome path.1))).trans
      (StoredWordReset.storedWordReset_events (QubitLayout.canonical width) (outcome path.1))

/-- Its independent allowance contains at most one X correction per existing numerator bit. -/
theorem reset_budget (width : Nat) (path : (reset width).Path) :
    (reset width).resourcePool path ≤ width •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) := by
  rw [reset_cost]
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [ResourcePool.count_nsmul, ResourcePool.count_nsmul]
  exact Nat.mul_le_mul_right _ (EncodedBit.Word.BasisLoad.basisLoad_count_le (outcome path.1))

end

end QuantumAlg.MeasuredUncompute.NumeratorReset
