/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Circuit

/-!
# Complete chronological record of actual small-base preparation

Every original doubling consumes its predecessor's actual returned Store
and service state. The existing finite-range interpreter combines these
same records, preserving the original history and arbitrary Reference.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The original two native coordinate copies retain their actual intermediate Store. -/
def seedRecord (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length) :
    Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.seedCircuit (model := model) sourceX sourceY row).Path :=
  Circuit.sequenceRecord
    (BitWord.instruction (execution := model) (rowWriteOp frame.x row sourceX))
    (BitWord.instruction (execution := model) (rowWriteOp frame.y row sourceY))
    (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (rowWriteOp frame.x row sourceX)))
    (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (rowWriteOp frame.y row sourceY)))

/-- These two actual copies retain all original matrix blocks and full history. -/
lemma seedCircuit_execute (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.seedCircuit (model := model) sourceX sourceY row).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.seedRecord sourceX sourceY row (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord (environment := environment)
  · intro reference history historyFinite initial
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model) _ initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history historyFinite initial
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model) _ initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- Every one of the sixteen real doubling calls retains its actual chronological record. -/
def baseStepRecord (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.baseStep (model := model) spec source destination).Path :=
  Circuit.sequenceRecord (frame.doubleCircuit spec source destination)
    (Circuit.forRange 15 (fun _ => frame.doubleCircuit spec destination destination))
    (frame.doubleRecord spec source destination environment)
    (Circuit.forRangeRecord 15 (fun _ => frame.doubleCircuit spec destination destination)
      (fun _ => frame.doubleRecord spec destination destination environment))

/-- The actual sixteen-doubling block uses those same true intermediate Stores and paths. -/
lemma baseStep_execute (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.baseStep (model := model) spec source destination).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.baseStepRecord spec source destination environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord (environment := environment)
  · exact frame.doubleCircuit_execute spec source destination environment
  · exact Circuit.execute_forRangeRecord 15
      (fun _ => frame.doubleCircuit spec destination destination) environment
      (fun _ => frame.doubleRecord spec destination destination environment)
      (fun _ => frame.doubleCircuit_execute spec destination destination environment)

variable {baseCount : Nat} (frame : CoordinateFrame ctx width (baseCount + 1))

/-- Complete record of the actual original copies and every paid next-base preparation. -/
def prepareBasesRecord (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.prepareBases (model := model) spec sourceX sourceY).Path :=
  Circuit.sequenceRecord (frame.seedCircuit sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩)
    (Circuit.forRange baseCount (fun index => frame.baseStep spec index.castSucc index.succ))
    (frame.seedRecord sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩)
    (Circuit.forRangeRecord baseCount
      (fun index => frame.baseStep spec index.castSucc index.succ)
      (fun index => frame.baseStepRecord spec index.castSucc index.succ environment))

/-- Full small-base preparation retains arbitrary original quantum/reference/history blocks. -/
lemma prepareBases_execute (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.prepareBases (model := model) spec sourceX sourceY).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.prepareBasesRecord spec sourceX sourceY environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord (environment := environment)
  · exact frame.seedCircuit_execute sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩ environment
  · exact Circuit.execute_forRangeRecord baseCount
      (fun index => frame.baseStep spec index.castSucc index.succ) environment
      (fun index => frame.baseStepRecord spec index.castSucc index.succ environment)
      (fun index => frame.baseStep_execute spec index.castSucc index.succ environment)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
