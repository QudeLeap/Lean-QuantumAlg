/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Tangent
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Identity

/-!
# Complete retained record of the actual original five-table program

Every original layer, negative tangent denominator, paid batch inverse,
final column overwrite and explicit identity-row clear consumes its actual
predecessor. This is the existing program, with every intermediate actual
Store, service state, full chronological path and external Reference kept.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The last original batch visits all and only the positive original table addresses. -/
lemma finalBatchFits : 2 ^ window - 1 < 2 ^ window := by
  have := Nat.two_pow_pos window
  omega

/-- Actual record of every binary coordinate-construction layer. -/
def coordinateLayersRecord (spec : ModulusSpec width) (environment : model.Environment) :=
  Circuit.forRangeRecord window (frame.layerCircuit (model := model) spec)
    (fun level => frame.layerRecord spec level environment)

/-- All original binary layers retain their complete actual history and arbitrary Reference. -/
lemma coordinateLayers_execute (spec : ModulusSpec width) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange window (frame.layerCircuit (model := model) spec)).execute environment
      Reference state = state.mapClassical (fun entry =>
        let result := frame.coordinateLayersRecord spec environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord window _ environment _
    (fun level => frame.layerCircuit_execute spec level environment) Reference state

/-- Actual record of every original final negative-tangent denominator. -/
def finalDenominatorsRecord (spec : ModulusSpec width) (environment : model.Environment) :=
  Circuit.forRangeRecord (2 ^ window - 1)
    (fun index => frame.tangentDenominatorRow (model := model) (nonzeroRow window index))
    (fun index => frame.tangentRecord spec (nonzeroRow window index) environment)

/-- Every actual final denominator retains the same complete incoming history and Reference. -/
lemma finalDenominators_execute (spec : ModulusSpec width) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange (2 ^ window - 1) (fun index =>
      frame.tangentDenominatorRow (model := model) (nonzeroRow window index))).execute environment
      Reference state = state.mapClassical (fun entry =>
        let result := frame.finalDenominatorsRecord spec environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (2 ^ window - 1) _ environment _
    (fun index => frame.tangentDenominatorRow_execute spec (nonzeroRow window index) environment)
    Reference state

/-- Actual record of every original in-place five-column conversion. -/
def finishRowsRecord (spec : ModulusSpec width) (environment : model.Environment) :=
  Circuit.forRangeRecord (2 ^ window - 1)
    (fun index => frame.finishRow (model := model) (nonzeroRow window index))
    (fun index => frame.finishRecord spec (nonzeroRow window index) environment)

/-- All original final column writes retain their complete actual history and external Reference. -/
lemma finishRows_execute (spec : ModulusSpec width) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange (2 ^ window - 1) (fun index =>
      frame.finishRow (model := model) (nonzeroRow window index))).execute environment Reference
      state = state.mapClassical (fun entry =>
        let result := frame.finishRowsRecord spec environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (2 ^ window - 1) _ environment _
    (fun index => frame.finishRow_execute spec (nonzeroRow window index) environment)
    Reference state

/-- Complete original chronology, including the true zero-width path and identity-row clear. -/
def circuitRecord (spec : ModulusSpec width) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.circuit (model := model) spec).Path :=
  Circuit.sequenceRecord (Circuit.forRange window (frame.layerCircuit spec))
    (.seq (Circuit.forRange (2 ^ window - 1) (fun index =>
      frame.tangentDenominatorRow (nonzeroRow window index)))
      (.seq (frame.batch.circuit spec (2 ^ window - 1) finalBatchFits)
        (.seq (Circuit.forRange (2 ^ window - 1) (fun index =>
          frame.finishRow (nonzeroRow window index)))
          (frame.clearIdentityRow ⟨0, Nat.two_pow_pos window⟩))))
    (frame.coordinateLayersRecord spec environment)
    (Circuit.sequenceRecord _ _ (frame.finalDenominatorsRecord spec environment)
      (Circuit.sequenceRecord _ _
        (frame.batch.valueRecord spec (2 ^ window - 1) finalBatchFits environment)
        (Circuit.sequenceRecord _ _ (frame.finishRowsRecord spec environment)
          (frame.clearIdentityRecord ⟨0, Nat.two_pow_pos window⟩))))

/-- The full existing five-table program executes this same complete actual retained record. -/
lemma tableCircuit_execute (spec : ModulusSpec width) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.circuit (model := model) spec).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.circuitRecord spec environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord
  · exact frame.coordinateLayers_execute spec environment
  · apply Circuit.execute_sequenceRecord
    · exact frame.finalDenominators_execute spec environment
    · apply Circuit.execute_sequenceRecord
      · exact frame.batch.circuit_execute spec (2 ^ window - 1) finalBatchFits environment
      · exact Circuit.execute_sequenceRecord _ _ environment _ _
          (frame.finishRows_execute spec environment)
          (frame.clearIdentityRow_execute ⟨0, Nat.two_pow_pos window⟩ environment)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
