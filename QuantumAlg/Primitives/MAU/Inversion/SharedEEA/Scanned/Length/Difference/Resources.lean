/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Actual native resources of the physically placed overflow subtraction -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The existing-word placement retains the entire original native event pool. -/
lemma program_eventCost (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    (program width length fits).eventCost =
      (Addition.TTK.overflowSubtractionProgram length).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Every actual borrow-output subtraction gate is charged, including its top Toffoli. -/
lemma program_toffoli_count (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width length fits).eventCost =
        2 * (length - 1) + (if length = 0 then 0 else 1) := by
  rw [program_eventCost, Addition.TTK.ttkOverflowSubtraction_native_count,
    Addition.TTK.ttkOverflow_toffoli_count]

/-- Native CNOT multiplicity includes the actual high carry precondition gate. -/
lemma program_cnot_count (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width length fits).eventCost =
        length + 2 * (length - 1) + 2 * (length - 2) + (if 2 ≤ length then 1 else 0) := by
  rw [program_eventCost, Addition.TTK.ttkOverflowSubtraction_native_count,
    Addition.TTK.ttkOverflow_cnot_count]

/-- This original serial native word contains no single-qubit instruction. -/
lemma program_singleQubit_count (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width length fits).eventCost = 0 := by
  rw [program_eventCost, Addition.TTK.ttkOverflowSubtraction_native_count,
    Addition.TTK.ttkOverflow_native_count]
  simp

/-- Placement retains the actual original serial dependency schedule. -/
lemma program_unitDepth (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) :
    (program width length fits).evaluatedEventDepth (fun _ => 1) =
      length + 4 * (length - 1) + 2 * (length - 2) +
        (if 2 ≤ length then 1 else 0) + (if length = 0 then 0 else 1) := by
  rw [program, WireSubsystem.program_evaluatedEventDepth]
  exact (Addition.TTK.ttkOverflowSubtraction_serial_resources length).2

/-- Default quantum duration equals that native list's actual unit dependency duration. -/
lemma program_quantumTime (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) :
    (program width length fits).evaluatedEventDepth Resource.Event.quantumDuration =
      length + 4 * (length - 1) + 2 * (length - 2) +
        (if 2 ≤ length then 1 else 0) + (if length = 0 then 0 else 1) := by
  exact (UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (program width length fits) .empty .empty).trans (program_unitDepth width length fits)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
