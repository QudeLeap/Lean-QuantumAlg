/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Denominator
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Total

/-!
# Complete chronological records of the original binary construction layers

Each seed preparation feeds its actual Store to every denominator row,
the original total batch inverse and each real coordinate extension.
The complete original path is retained, including the genuine empty batch
at the first layer. Arbitrary incoming Store, service state, history and
external Reference are preserved by the same actual execution equation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The original batch visits exactly the old positive rows strictly below the current seed. -/
lemma layerFits (level : Fin window) : layerCount level < 2 ^ window := by
  have seed := (layerSeed window level).isLt
  have positive := Nat.two_pow_pos level.val
  dsimp only [layerSeed] at seed
  dsimp only [layerCount]
  omega

/-- Actual chronological record of every original denominator in this binary layer. -/
def layerDenominatorsRecord (level : Fin window) (environment : model.Environment) :=
  Circuit.forRangeRecord (layerCount level)
    (fun index => frame.denominatorRow (model := model)
      (layerSeed window level) (oldRow level index))
    (fun index => Circuit.preserveHiddenRecord
      (frame.denominatorRecord (layerSeed window level) (oldRow level index) environment))

/-- All actual denominator rows retain the original full history and Reference blocks. -/
lemma layerDenominators_execute (level : Fin window) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange (layerCount level) (fun index =>
      frame.denominatorRow (model := model) (layerSeed window level) (oldRow level index))).execute
      environment Reference state = state.mapClassical (fun entry =>
        let result := frame.layerDenominatorsRecord level environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_forRangeRecord
  intro index reference history historyFinite initial
  exact (frame.denominatorRow_execute (layerSeed window level) (oldRow level index) environment
    reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- Actual chronological record of each original nonseed coordinate extension. -/
def layerExtensionsRecord (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) :=
  Circuit.forRangeRecord (layerCount level)
    (fun index => frame.extendRow (model := model) (layerSeed window level)
      (oldRow level index) (newRow level index))
    (fun index => frame.extendRecord spec (layerSeed window level) (oldRow level index)
      (newRow level index) environment)

/-- All actual coordinate extensions retain the same complete incoming history and Reference. -/
lemma layerExtensions_execute (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange (layerCount level) (fun index => frame.extendRow (model := model)
      (layerSeed window level) (oldRow level index) (newRow level index))).execute environment
      Reference state = state.mapClassical (fun entry =>
        let result := frame.layerExtensionsRecord spec level environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (layerCount level) _ environment _
    (fun index => frame.extendRow_execute spec (layerSeed window level) (oldRow level index)
      (newRow level index) environment) Reference state

/-- The original four actual stages retain their complete chronological Stores and paths. -/
def layerRecord (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) × (frame.layerCircuit (model := model) spec level).Path :=
  Circuit.sequenceRecord (frame.prepareSeed spec level)
    (.seq (Circuit.forRange (layerCount level) (fun index =>
      frame.denominatorRow (layerSeed window level) (oldRow level index)))
      (.seq (frame.batch.circuit spec (layerCount level) (layerFits level))
        (Circuit.forRange (layerCount level) (fun index =>
          frame.extendRow (layerSeed window level) (oldRow level index) (newRow level index)))))
    (frame.prepareSeedRecord spec level environment)
    (Circuit.sequenceRecord _ _ (frame.layerDenominatorsRecord level environment)
      (Circuit.sequenceRecord _ _
        (frame.batch.valueRecord spec (layerCount level) (layerFits level) environment)
        (frame.layerExtensionsRecord spec level environment)))

/-- The same actual original layer retains arbitrary incoming quantum/reference/history blocks. -/
lemma layerCircuit_execute (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.layerCircuit (model := model) spec level).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.layerRecord spec level environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord
  · exact frame.prepareSeed_execute spec level environment
  · apply Circuit.execute_sequenceRecord
    · exact frame.layerDenominators_execute level environment
    · exact Circuit.execute_sequenceRecord _ _ environment _ _
        (frame.batch.circuit_execute spec (layerCount level) (layerFits level) environment)
        (frame.layerExtensions_execute spec level environment)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
