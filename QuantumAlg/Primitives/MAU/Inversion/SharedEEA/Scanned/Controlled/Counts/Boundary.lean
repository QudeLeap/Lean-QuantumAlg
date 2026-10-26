/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Components
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Predicates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Refresh.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Boundary

/-!
# Native X coordinates of the complete actual four-write boundary refresh

Every encoder mask, public boundary load, negative activation mask and
output-copy mask is counted in its actual preparation/copy/adjoint order.
Both coefficient and both divisor writers execute. Arbitrary retained
source fields and inactive quantum controls do not remove any occurrence.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

private lemma uncontrolled_gates_x_count {Data : Type} {frame : BinaryLabelEncoding Data}
    {size : Nat} (placement : PermutationFrame frame size)
    (exchanges : List (Permutation.Transposition (Fin size))) :
    ((placement.uncontrolledGates exchanges).map GateSpec.xMultiplicity).sum = 0 := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (placement.uncontrolledGates exchanges)
  rw [GateSpec.primitiveEventCount, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_x_count_eq_sum] at native
  have actual := placement.uncontrolled_counts exchanges
  omega

/-- Actual public transpositions contain only their three native CNOT leaves. -/
lemma length_alignment_public_x_count (width : Nat) (field : LengthCoordinates.Field)
    (first : Bool) :
    ((LengthAlignment.publicGates width field first).map GateSpec.xMultiplicity).sum = 0 := by
  cases field
  · rfl
  · exact uncontrolled_gates_x_count _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

/-- Neither the actual metadata barrel nor the paid public rotation emits an X gate. -/
lemma program_singleQubit_count (width : Nat) (field : Field) (first : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width field first).eventCost = 0 := by
  rw [program, GateSpec.programList_x_count_eq_sum, gates, List.map_append, List.sum_append,
    ControlledCounts.length_alignment_public_x_count]
  simp only [barrelGates, ControlledCounts.barrel_gates_x_count, Nat.zero_add]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- All native X gates in this actual boundary preparation are its literal public loader. -/
lemma prepareProgram_singleQubit_count (width : Nat) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (prepareProgram width field).eventCost = constantWeight width field := by
  have inverse :
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (placement width field).subtractProgram.eventCost = 0 := by
    rw [Addition.TTK.WordPlacement.subtractProgram_eventCost]
    simpa using Addition.TTK.ttkLowRipple_native_count (ScanMetadata.addressWidth width)
      (.gate .singleQubit)
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, inverse,
    Nat.add_zero, constantProgram, Word.xorConstantProgram,
    GateSpec.programList_x_count_eq_sum, Word.xorConstantGates_xMultiplicity_sum]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates

private lemma p256_activation_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (activationProgram 256).eventCost = 2 := by
  rw [activationProgram, activationGates, if_pos (by decide : narrow 256),
    GateSpec.programList_eventCost, activeGates_events, ResourcePool.count_ofList]
  decide

/-- Full clipping retains the public load and both real negative high-bit masks. -/
lemma p256_prepareProgram_singleQubit_count (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (prepareProgram 256 field).eventCost = LengthBoundary.constantWeight 256 field + 2 := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    LengthBoundary.prepareProgram_singleQubit_count, p256_activation_singleQubit_count,
    LengthDifference.program_singleQubit_count, Nat.add_zero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

noncomputable section

open LengthCoordinates NumberTheory.SharedEEA

/-- The real encoder X gates and clipping masks remain in each complete preparation. -/
lemma p256_program_singleQubit_count (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 field first capacity).eventCost =
        4198 + LengthBoundary.constantWeight 256 field := by
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add, LengthAlignment.program_singleQubit_count,
    (LengthEncoder.p256_counts field first capacity).2.2,
    LengthClip.p256_prepareProgram_singleQubit_count]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

noncomputable section

open LengthCoordinates NumberTheory.SharedEEA

/-- Both complete preparations and the output-copy X masks execute in the actual writer. -/
lemma p256_program_singleQubit_count (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 field first capacity).eventCost =
        8398 + 2 * LengthBoundary.constantWeight 256 field := by
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_nsmul,
    LengthPrepare.p256_program_singleQubit_count,
    (LengthCopy.program_resources 256 (decide (LengthClip.narrow 256)) field).2.2.1]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh

noncomputable section

open NumberTheory.SharedEEA

/-- All four original coefficient/divisor writers retain their complete native X ledgers. -/
lemma p256_program_singleQubit_count
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 capacity).eventCost = 33612 := by
  have weights : LengthBoundary.constantWeight 256 .coefficient = 3 ∧
      LengthBoundary.constantWeight 256 .divisor = 2 := by decide
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    LengthRefreshWrite.p256_program_singleQubit_count, weights.1, weights.2]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh
