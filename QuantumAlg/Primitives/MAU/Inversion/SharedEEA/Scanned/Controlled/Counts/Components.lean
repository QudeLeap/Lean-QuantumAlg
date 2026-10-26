/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Resources
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Resources

/-! # Shared source multiplicities and actual address coordinates -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

private lemma permutation_gates_x_count {Data : Type} {frame : BinaryLabelEncoding Data}
    {size : Nat} (placement : PermutationFrame frame size)
    (exchanges : List (Permutation.Transposition (Fin size))) :
    ((placement.gates exchanges).map GateSpec.xMultiplicity).sum = 0 := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (placement.gates exchanges)
  rw [GateSpec.primitiveEventCount, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_x_count_eq_sum] at native
  have actual := placement.gates_counts exchanges
  omega

/-- Every actual barrel stage is a native Fredkin word, so it has no X instruction. -/
lemma barrel_gates_x_count {Data : Type} {frame : BinaryLabelEncoding Data} {size controls : Nat}
    (barrel : PermutationBarrel frame size controls) (permutation : Equiv.Perm (Fin size))
    (stages : List (Fin controls × Nat)) :
    ((barrel.gates permutation stages).map GateSpec.xMultiplicity).sum = 0 := by
  induction stages with
  | nil => rfl
  | cons stage rest ih =>
      simp only [PermutationBarrel.gates, List.map_append, List.sum_append,
        PermutationBarrel.stageGates, permutation_gates_x_count, ih, Nat.zero_add]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma subtractProgram_singleQubit_count (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (subtractProgram width positive field).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (placement width positive field).subtractProgram.eventCost = 0
  rw [Addition.TTK.WordPlacement.subtractProgram_eventCost]
  simpa using Addition.TTK.ttkLowRipple_native_count (ScanMetadata.addressWidth width)
    (.gate .singleQubit)

private lemma constantProgram_singleQubit_count (width : Nat)
    (constant : BitVec (ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (constantProgram width constant).eventCost =
        (Word.constantOneIndices constant.toFin).length := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_x_count_eq_sum,
    Word.xorConstantGates_xMultiplicity_sum]

/-- The actual remainder address preparation charges both set bits of its public constant. -/
lemma p256_remainderProgram_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (remainderProgram 256 (by decide)).eventCost = 2 := by
  simp only [remainderProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    subtractProgram_singleQubit_count, Nat.add_zero, constantProgram_singleQubit_count]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
