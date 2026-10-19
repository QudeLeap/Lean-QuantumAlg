/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.State.History

/-!
# Exact measurement paths across allocation permissions

The same finite readout list performs the same actual Z measurements and
classical writes. Allocation permission changes neither the measurements nor
the complete resulting state. The explicit recursive outcome correspondence
retains every Store, persistent service, old history and quantum reference.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {allowLeft allowRight : Bool} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  (environment :
    (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
  {ctx : RuntimeCtx .quantum}

/-- The identical ordered measurements have exactly corresponding finite outcomes. -/
def measurementSequencePermissionPathEquiv : (readouts : List (ZReadout ctx)) →
    (measurementSequence (allowAllocation := allowLeft) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).Path ≃
    (measurementSequence (allowAllocation := allowRight) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).Path
  | [] => Equiv.refl _
  | _head :: tail => Equiv.prodCongr (Equiv.refl _)
      (measurementSequencePermissionPathEquiv tail)

/-- The full actual state differs only in its explicitly corresponding outcome-path type. -/
lemma measurementSequence_permission_execute (readouts : List (ZReadout ctx))
    (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H)) :
    (measurementSequence (allowAllocation := allowRight) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).execute
        environment Reference state =
      ((measurementSequence (allowAllocation := allowLeft) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts).execute
          environment Reference state).mapHistory (fun record =>
            (record.1, (record.2.1,
              measurementSequencePermissionPathEquiv (allowLeft := allowLeft)
                (allowRight := allowRight) readouts record.2.2))) := by
  induction readouts generalizing H with
  | nil =>
      simp only [measurementSequence, execute_id, State.mapHistory,
        ExecutionState.executionState_mapClassical_comp]
      exact State.mapClassical_decision _ _ state _
  | cons head tail ih =>
      simp only [measurementSequence, execute_seq, execute_measureZ]
      rw [ih]
      simp only [State.mapHistory_comp]
      rfl

/-- The same basis label produces exactly the same complete ordered Store writes. -/
lemma measurementWriteBasis_permission (readouts : List (ZReadout ctx))
    (store : Store ctx) (basis : ctx.register.Index) :
    writeMeasurementPath (allowAllocation := allowRight) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts store
      (measurementBasisPath (allowAllocation := allowRight) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts basis) =
    writeMeasurementPath (allowAllocation := allowLeft) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts store
      (measurementBasisPath (allowAllocation := allowLeft) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts basis) := by
  induction readouts generalizing store with
  | nil => rfl
  | cons head tail ih =>
      exact ih (store.write head.output (.finite (basis head.wire)))

end

end QuantumAlg.Circuit
