/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Indexed
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual chronological preparation records for both original base families

The same real constant loaders, increment and paired-base circuits retain
their complete Store, service-state and Path updates. Both base families
use the same four scalar words, and the second preparation receives the
first preparation's actual returned state. Arbitrary quantum/reference
blocks and incoming histories remain intact.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

private def constantRecord {size : Nat} (output : CWriteRef ctx (.unsignedWord size))
    (constant : Nat) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (ConstantWord.circuit (model := model) output constant).Path :=
  Circuit.preserveHiddenRecord (ConstantWord.foldStep (model := model) output
    (List.ofFn (ConstantWord.constantBits size constant)))

/-- Original actual loaders and increment, with their complete chronological intermediate states. -/
def initializationRecord (spec : ModulusSpec width) (coefficient : Nat) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.initializeConstants (model := model) spec coefficient).Path :=
  Circuit.sequenceRecord (ConstantWord.circuit frame.modulus spec.modulus)
    (.seq (ConstantWord.circuit frame.curveA coefficient)
      (BitWord.instruction (ConstantWord.incrementOp frame.one)))
    (constantRecord frame.modulus spec.modulus)
    (Circuit.sequenceRecord (ConstantWord.circuit frame.curveA coefficient)
      (BitWord.instruction (ConstantWord.incrementOp frame.one))
      (constantRecord frame.curveA coefficient)
      (Circuit.preserveHiddenRecord (BitWord.instructionStep
        (execution := model) (ConstantWord.incrementOp frame.one))))

/-- Complete actual preparation of both retained seventeen-row families. -/
def pairedBasesRecord (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).Path :=
  Circuit.sequenceRecord
    (frame.coordinates.prepareBasesAt spec firstX firstY (@firstBaseRows 16))
    (frame.coordinates.prepareBasesAt spec secondX secondY (@secondBaseRows 16))
    (frame.coordinates.prepareBasesAtRecord (model := model) spec firstX firstY
      (@firstBaseRows 16) environment)
    (frame.coordinates.prepareBasesAtRecord (model := model) spec secondX secondY
      (@secondBaseRows 16) environment)

attribute [local irreducible] CoordinateFrame.prepareBasesAtRecord CoordinateFrame.prepareBasesAt

omit [BitWord.Selected model] in
private lemma sequenceRecord_state (first second : Circuit model ctx ctx)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (before : Store ctx × model.HiddenState) :
    (Circuit.sequenceRecord first second firstStep secondStep before).1 =
      (secondStep (firstStep before).1).1 := rfl

/-- The second original base family receives the first family's actual returned state. -/
lemma pairedBasesRecord_state (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.pairedBasesRecord spec firstX firstY secondX secondY environment before).1 =
      (frame.coordinates.prepareBasesAtRecord spec secondX secondY (@secondBaseRows 16)
        environment (frame.coordinates.prepareBasesAtRecord spec firstX firstY
          (@firstBaseRows 16) environment before).1).1 :=
  sequenceRecord_state
    (frame.coordinates.prepareBasesAt spec firstX firstY (@firstBaseRows 16))
    (frame.coordinates.prepareBasesAt spec secondX secondY (@secondBaseRows 16))
    (frame.coordinates.prepareBasesAtRecord (model := model) spec firstX firstY
      (@firstBaseRows 16) environment)
    (frame.coordinates.prepareBasesAtRecord (model := model) spec secondX secondY
      (@secondBaseRows 16) environment) before

/-- Actual paired preparation retains every original quantum/reference/history matrix block. -/
lemma preparePairedBases_execute (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).execute
      environment Reference state = state.mapClassical (fun entry =>
        let result := frame.pairedBasesRecord spec firstX firstY secondX secondY environment
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold preparePairedBases pairedBasesRecord
  apply Circuit.execute_sequenceRecord
  · exact frame.coordinates.prepareBasesAt_execute spec firstX firstY
      (@firstBaseRows 16) environment
  · exact frame.coordinates.prepareBasesAt_execute spec secondX secondY
      (@secondBaseRows 16) environment

/-- Actual loading retains every original quantum/reference/history block and its actual path. -/
lemma initializeConstants_execute (spec : ModulusSpec width) (coefficient : Nat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.initializeConstants (model := model) spec coefficient).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.initializationRecord spec coefficient (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord
  · intro reference history _ initial
    exact ConstantWord.constantWord_fold_execute frame.modulus _ reference initial
  · apply Circuit.execute_sequenceRecord
    · intro reference history _ initial
      exact ConstantWord.constantWord_fold_execute frame.curveA _ reference initial
    · intro reference history _ initial
      exact (BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
        (ConstantWord.incrementOp frame.one) initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame
