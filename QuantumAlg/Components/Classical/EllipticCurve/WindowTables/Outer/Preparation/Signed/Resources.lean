/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Accounting
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Arithmetic
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Preparation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Time
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Cardinality

/-!
# Actual native accounting of the paid signed-row prefix

The two nominal point unpacks and the negative target-coordinate subtraction
are paid before both complete seventeen-row preparations. All counts refer
to the same actual prefix and its original lexical paths. The classical
instructions contribute zero quantum gates, measurements and quantum time.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open WindowTables.Outer.QuantumAccounting

/-- Actual constant loads, two point unpacks, two subtraction loaders and both base families. -/
def classicalLimit (width : Nat) : Nat :=
  8 * width + 15 + 2 * (2 + 16 * (16 * (30 * width + 127)))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma subtraction_count_zero
    (focus : Resource.Event model)
    (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)
    (spec : ModulusSpec width) (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (Field.Native.subIntoWord (model := model) spec left right output).Path) :
    ResourcePool.count focus
      ((Field.Native.subIntoWord (model := model) spec left right output).resourcePool path) =
        0 := by
  rw [Field.Native.subIntoWord_resourcePool]
  simp [Field.Native.subtractionTrace, Field.Native.subtractionPrefixTrace,
    Field.Native.loadedReductionTrace, ClassicalRoutines.Modular.Reduce.Native.reductionEvents,
    loader_count_zero focus nativeFree,
    fun coordinate => (nativeFree coordinate).symm]

/-- The actual full prefix emits only native classical operation events. -/
lemma prepare_count_zero (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat) (base target : CInputRef ctx (PointShape width))
    (focus : Resource.Event model)
    (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)
    (path : (prepare (model := model) frame spec coefficient base target).Path) :
    ResourcePool.count focus
      ((prepare (model := model) frame spec coefficient base target).resourcePool path) = 0 := by
  unfold prepare at path ⊢
  apply seq_count_zero focus
  · exact initialization_count_zero focus nativeFree frame spec coefficient path.1
  · exact withCellsFrom_property (Transport.id ctx) (scratchShapes width) _
      (fun _ code => ∀ selected, ResourcePool.count focus (code.resourcePool selected) = 0)
      (fun _ _ _ _ _ available => available)
      (by
        intro inner cells distinct lift separated selected
        apply seq_count_zero focus
        · exact instruction_count_zero focus nativeFree _ _
        · apply seq_count_zero focus
          · exact instruction_count_zero focus nativeFree _ _
          · apply seq_count_zero focus
            · exact subtraction_count_zero focus nativeFree _ _ _ _ _
            · exact pairedBases_count_zero focus nativeFree _ _ _ _ _ _ _) path.2

/-- Zero quantum duration follows from the actual prefix's native event pools. -/
lemma prepare_quantumTime_zero (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat) (base target : CInputRef ctx (PointShape width))
    (path : (prepare (model := model) frame spec coefficient base target).Path) :
    (prepare (model := model) frame spec coefficient base target).quantumTime path = 0 := by
  exact quantumTime_zero _
    (fun focus nativeFree selected =>
      prepare_count_zero frame spec coefficient base target focus nativeFree selected) path

private lemma subtraction_classical_le (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (Field.Native.subIntoWord (model := model) spec left right output).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Field.Native.subIntoWord (model := model) spec left right output).resourcePool path) ≤
        4 * width + 10 := by
  have actual := WindowTables.Accounting.classical_weight_le_eventCount
    (Field.Native.subIntoWord (model := model) spec left right output) path
  rw [Field.Native.fieldSubIntoWord_eventTrace] at actual
  exact actual.trans (Field.Native.subtractionTrace_length_le model spec)

/-- All actual native work of the original signed prefix has its derived width bound. -/
lemma prepare_classical_le (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat) (base target : CInputRef ctx (PointShape width))
    (path : (prepare (model := model) frame spec coefficient base target).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((prepare (model := model) frame spec coefficient base target).resourcePool path) ≤
        classicalLimit width := by
  unfold prepare at path ⊢
  have constants := frame.initializeConstants_classical_weight_le spec coefficient path.1
  have body : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((withCells (model := model) ctx (scratchShapes width) fun
        {inner} cells _ lift _ =>
          let scratch := scratchOfCells cells
          let localFrame := frame.transport lift
          .seq
            (BitWord.instruction (execution := model)
              (.unpackEllipticCurvePoint width inner (lift.liftInput base) scratch.rawBase))
            (.seq
              (BitWord.instruction (execution := model)
                (.unpackEllipticCurvePoint width inner (lift.liftInput target) scratch.rawTarget))
              (.seq
                (Field.Native.subIntoWord spec (.storage localFrame.zero.toCStorageRef)
                  (rawY scratch.rawTarget) scratch.signedY)
                (localFrame.preparePairedBases spec
                  (rawX scratch.rawBase) (rawY scratch.rawBase)
                  (rawX scratch.rawTarget) (.storage scratch.signedY.toCStorageRef))))).resourcePool
          path.2) ≤
        2 + (4 * width + 10) + 2 * (2 + 16 * (16 * (30 * width + 127))) := by
    apply Accounting.allocation_weight_le (Transport.id ctx) (scratchShapes width) _
      Resource.Event.classicalOperationWeight
    intro inner cells distinct lift separated selected
    have unpackBase := WindowTables.Accounting.classical_weight_le_eventCount _ selected.1
    rw [WindowTables.Accounting.instruction_eventCount] at unpackBase
    have unpackTarget := WindowTables.Accounting.classical_weight_le_eventCount _ selected.2.1
    rw [WindowTables.Accounting.instruction_eventCount] at unpackTarget
    have negative := subtraction_classical_le _ _ _ _ selected.2.2.1
    have rows := (frame.transport lift).preparePairedBases_classical_weight_le
      _ _ _ _ _ selected.2.2.2
    have tail := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
      _ _ selected.2.2 negative rows
    have rest := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
      1 _ selected.2 unpackTarget tail
    exact (Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
      1 _ selected unpackBase rest).trans_eq (by omega)
  exact (Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
    _ _ path constants body).trans_eq (by unfold classicalLimit; omega)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
