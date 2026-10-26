/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Write
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Resources
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Resources

/-! # Resources of complete actual native length compute/copy/adjoint -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Both preparations and every real finite output-copy gate occur in the actual native word. -/
lemma program_eventCost (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    (program width field first capacity).eventCost =
      2 • (LengthPrepare.program width field first capacity).eventCost +
        (LengthCopy.program width (decide (LengthClip.narrow width)) field).eventCost := by
  rw [program, WordCompute.program, PredicateCompute.program_eventCost]

/-- The actual native adjoint retains the dependency duration of all parallel source blocks. -/
lemma program_quantumTime (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    (program width field first capacity).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (LengthPrepare.program width field first capacity).evaluatedEventDepth
        Resource.Event.quantumDuration + 4 * width.size + 2 := by
  rw [program, WordCompute.program, PredicateCompute.program_quantumTime,
    (LengthCopy.program_resources width (decide (LengthClip.narrow width)) field).2.2.2]
  omega

/-- This bound charges actual preparation, copy and inverse, with no finite selector enumeration. -/
lemma p256_program_toffoli_count_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 field first capacity).eventCost ≤ 20506 := by
  have preparation := LengthPrepare.p256_program_toffoli_count_le field first capacity
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_nsmul,
    (LengthCopy.program_resources 256 (decide (LengthClip.narrow 256)) field).1]
  have numeric : (256 : Nat).size = 9 := by decide
  rw [numeric]
  omega

/-- Actual native CNOT accounting retains both complete public divisor exchanges. -/
lemma p256_program_cnot_count_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 field first capacity).eventCost ≤
        10530 + 2 * LengthAlignment.publicBudget 256 field := by
  have preparation := LengthPrepare.p256_program_cnot_count_le field first capacity
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_nsmul,
    (LengthCopy.program_resources 256 (decide (LengthClip.narrow 256)) field).2.1]
  omega

/-- Default time follows the complete actual native prepare/copy/uncompute schedule. -/
lemma p256_program_quantumTime_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    (program 256 field first capacity).evaluatedEventDepth Resource.Event.quantumDuration ≤
      39406 + 2 * LengthAlignment.publicBudget 256 field := by
  have preparation := LengthPrepare.p256_program_quantumTime_le field first capacity
  rw [program_quantumTime]
  have numeric : (256 : Nat).size = 9 := by decide
  rw [numeric]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite
