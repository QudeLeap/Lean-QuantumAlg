/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Resources
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient.Runtime.Resources

/-!
# Additional native coordinates of the actual full-carry geometry words

The complete metadata TTK bodies have no X instructions. Public constant
loads retain their literal set-bit X counts. Runtime coherent selection
converts precisely those X gates into CNOTs and retains both actual
negative-control masks. These formulas concern the emitted original
programs and do not supply an alternative arithmetic implementation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- Both actual native TTK orientations contain no single-qubit instruction. -/
lemma nativeFieldGates_x_count (width : Nat) (positive : 1 ≤ width)
    (field : Field) (subtract : Bool) :
    ((nativeFieldGates width positive field subtract).map GateSpec.xMultiplicity).sum = 0 := by
  have placed := GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    (placement width positive field).nativeGates_eventTrace
  have source :
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (Addition.TTK.lowRippleProgram (fullWidth width)).eventCost = 0 := by
    simpa using Addition.TTK.ttkLowRipple_native_count (fullWidth width) (.gate .singleQubit)
  rw [Addition.TTK.lowRippleProgram, GateSpec.programList_x_count_eq_sum] at source
  cases subtract <;>
    simpa only [nativeFieldGates, Bool.false_eq_true, if_false, if_true,
      List.map_reverse, List.sum_reverse] using placed.trans source

/-- Exactly the set bits of the actual public constant emit native X instructions. -/
lemma nativeConstantGates_x_count (width : Nat) (constant : BitVec (fullWidth width)) :
    ((nativeConstantGates width constant).map GateSpec.xMultiplicity).sum =
      (Word.constantOneIndices constant.toFin).length :=
  (littleTarget width).xorConstantGates_xMultiplicity_sum constant.toFin

/-- Each fixed coefficient phase retains its own actual constant load. -/
lemma nativeCoefficientGates_x_count (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    ((nativeCoefficientGates width positive deshift).map GateSpec.xMultiplicity).sum =
      (Word.constantOneIndices (coefficientConstant width deshift).toFin).length := by
  cases deshift <;>
    simp only [nativeCoefficientGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, nativeConstantGates_x_count, nativeFieldGates_x_count,
      Nat.add_zero]

/-- The actual phase control converts its own public loader's X gates into CNOTs. -/
lemma phaseControlledGates_cnot_count (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    ((phaseControlledGates width positive deshift).map GateSpec.cnotMultiplicity).sum =
      (Word.constantOneIndices (coefficientConstant width deshift).toFin).length := by
  rw [phaseControlledGates, GateSpec.listWithDirtyControl_cnotMultiplicity_sum,
    nativeCoefficientGates_x_count]

/-- The original runtime word contains precisely the two literal negative-phase masks. -/
lemma runtimeCoefficientGates_x_count (width : Nat) (positive : 1 ≤ width) :
    ((runtimeCoefficientGates width positive).map GateSpec.xMultiplicity).sum = 2 := by
  simp only [runtimeCoefficientGates, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, GateSpec.xMultiplicity, phaseControlledGates,
    GateSpec.listWithDirtyControl_xMultiplicity_sum]

/-- Both actual phase-controlled public constants contribute to the runtime CNOT coordinate. -/
lemma runtimeCoefficientGates_cnot_count (width : Nat) (positive : 1 ≤ width) :
    ((runtimeCoefficientGates width positive).map GateSpec.cnotMultiplicity).sum =
      (Word.constantOneIndices (coefficientConstant width false).toFin).length +
        (Word.constantOneIndices (coefficientConstant width true).toFin).length := by
  simp only [runtimeCoefficientGates, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, GateSpec.cnotMultiplicity, phaseControlledGates_cnot_count, Nat.zero_add]

/-- The complete actual P-256 runtime coefficient geometry has four native CNOTs. -/
lemma p256_runtimeCoefficientProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (runtimeCoefficientProgram 256 (by decide)).eventCost = 4 := by
  rw [runtimeCoefficientProgram, GateSpec.programList_cnot_count_eq_sum,
    runtimeCoefficientGates_cnot_count]
  decide

/-- Both actual phase masks remain charged in the complete emitted program. -/
lemma p256_runtimeCoefficientProgram_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (runtimeCoefficientProgram 256 (by decide)).eventCost = 2 := by
  rw [runtimeCoefficientProgram, GateSpec.programList_x_count_eq_sum,
    runtimeCoefficientGates_x_count]

/-- The actual serial runtime geometry charges all three native coordinates. -/
lemma p256_runtimeCoefficientProgram_quantumTime :
    (runtimeCoefficientProgram 256 (by decide)).evaluatedEventDepth
      Resource.Event.quantumDuration = 393 := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty)
    (runtimeCoefficientGates 256 (by decide))
  change GateSpec.primitiveEventCount (runtimeCoefficientProgram 256 (by decide)) = _ at native
  rw [GateSpec.primitiveEventCount, runtimeCoefficientProgram_p256_toffoli,
    p256_runtimeCoefficientProgram_cnot_count,
    p256_runtimeCoefficientProgram_singleQubit_count] at native
  rw [runtimeCoefficientProgram, GateSpec.programList_quantumTime, ← native]

/-- Placement and native inverse preserve the TTK body's zero X coordinate. -/
lemma subtractProgram_singleQubit_count (width : Nat) (positive : 1 ≤ width) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (subtractProgram width positive field).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (placement width positive field).subtractProgram.eventCost = 0
  rw [Addition.TTK.WordPlacement.subtractProgram_eventCost]
  simpa using Addition.TTK.ttkLowRipple_native_count (fullWidth width) (.gate .singleQubit)

/-- The actual constant-load program emits one X for each selected constant bit. -/
lemma constantProgram_singleQubit_count (width : Nat) (constant : BitVec (fullWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (constantProgram width constant).eventCost =
        (Word.constantOneIndices constant.toFin).length := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_x_count_eq_sum,
    Word.xorConstantGates_xMultiplicity_sum]

/-- The complete three-subtraction remainder geometry retains the public loader's two X gates. -/
lemma p256_remainderProgram_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (remainderProgram 256 (by decide)).eventCost = 2 := by
  simp only [remainderProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    subtractProgram_singleQubit_count, Nat.add_zero, constantProgram_singleQubit_count]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
