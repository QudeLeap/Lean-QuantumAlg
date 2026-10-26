/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Placement

/-!
# Complete actual seed-preparation record in each original binary layer

The first seed uses the original two input copies. Every subsequent seed
uses the original fifteen paid doubling slots on the actual preceding
Store. The conditional is resolved only by the public binary level; its
record preserves all original histories and arbitrary Reference blocks.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The actual original doubling slots retain their real chronological Store and path. -/
def doubleRowRecord (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.doubleRow (model := model) spec source destination).Path :=
  RowInstruction.rangeRecord spec frame.modulus environment 15
    (frame.doubleInstructions source destination)

/-- The original full-builder and coordinate-only records return the identical actual state. -/
lemma doubleRowRecord_state (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.doubleRowRecord spec source destination environment before).1 =
      (frame.coordinates.doubleRecord spec source destination environment before).1 := rfl

/-- The original doubling retains every incoming history and Reference block. -/
lemma doubleRow_execute (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.doubleRow (model := model) spec source destination).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.doubleRowRecord spec source destination environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  RowInstruction.range_execute spec frame.modulus environment 15
    (frame.doubleInstructions source destination) Reference state

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

/-- Actual chronological record of the original public-level seed conditional. -/
def prepareSeedRecord (spec : ModulusSpec width) : (level : Fin window) →
    (environment : model.Environment) → Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (frame.prepareSeed (model := model) spec level).Path
  | ⟨0, bound⟩, _ => frame.coordinates.seedRecord frame.baseX frame.baseY
      (layerSeed window ⟨0, bound⟩)
  | ⟨level + 1, bound⟩, environment => frame.doubleRowRecord spec
      (previousSeed window ⟨level + 1, bound⟩) (layerSeed window ⟨level + 1, bound⟩) environment

/-- At the initial public level the actual state is exactly that of the two original copies. -/
lemma prepareSeedRecord_initial_state (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (initial : level.val = 0) :
    (frame.prepareSeedRecord spec level environment before).1 =
      (frame.coordinates.seedRecord frame.baseX frame.baseY (layerSeed window level) before).1 := by
  rcases level with ⟨value, bound⟩
  change value = 0 at initial
  subst value
  rfl

/-- At every later public level the actual state is that of the original paid doubling. -/
lemma prepareSeedRecord_later_state (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (later : level.val ≠ 0) :
    (frame.prepareSeedRecord spec level environment before).1 =
      (frame.coordinates.doubleRecord spec (previousSeed window level) (layerSeed window level)
        environment before).1 := by
  rcases level with ⟨value, bound⟩
  cases value with
  | zero => exact False.elim (later rfl)
  | succ value => exact frame.doubleRowRecord_state spec _ _ environment before

/-- Both original public branches retain the complete actual Store, path and external Reference. -/
lemma prepareSeed_execute (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.prepareSeed (model := model) spec level).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.prepareSeedRecord spec level environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  rcases level with ⟨value, bound⟩
  cases value with
  | zero =>
      exact (frame.coordinates.seedCircuit_execute frame.baseX frame.baseY
        (layerSeed window ⟨0, bound⟩) environment Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ value =>
      exact frame.doubleRow_execute spec (previousSeed window ⟨value + 1, bound⟩)
        (layerSeed window ⟨value + 1, bound⟩) environment Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
