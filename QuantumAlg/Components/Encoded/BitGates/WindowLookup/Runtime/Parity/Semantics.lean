/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Semantics

/-!
# Full actual records of runtime table parity

The second native instruction reads the AND result from its actual preceding
Store. Every native outcome, old history, hidden state and arbitrary external
reference remains in the same execution record.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

private lemma instruction_execute {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (MaskParity.instruction op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := MaskParity.instructionStep (oracles := oracles) (services := services)
          op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_classical_mapClassical environment (BitWord.application op) op.eval
    (BitWord.bitWord_application_evaluate op) Reference state

/-- The XOR outcome is obtained from the real Store returned by the AND instruction. -/
def stepRecord (parity temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) :
    Store ctx → Store ctx × (stepProgram (oracles := oracles) (services := services)
      parity temporary input).Path :=
  Circuit.sequenceStoreRecord (MaskParity.instruction (andOp temporary input))
    (MaskParity.instruction (MaskParity.xorOp parity (.storage temporary.toCStorageRef)))
    (MaskParity.instructionStep (andOp temporary input))
    (MaskParity.instructionStep (MaskParity.xorOp parity (.storage temporary.toCStorageRef)))

/-- The pair record preserves complete original quantum/reference blocks. -/
lemma stepProgram_execute (parity temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (stepProgram parity temporary input).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := stepRecord (oracles := oracles) (services := services)
          parity temporary input entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceStoreRecord _ _ environment
    (MaskParity.instructionStep (andOp temporary input))
    (MaskParity.instructionStep (MaskParity.xorOp parity (.storage temporary.toCStorageRef)))
    (instruction_execute _ environment) (instruction_execute _ environment) Reference state

/-- Every pair's actual outputs remain in chronological order. -/
def foldRecord (parity temporary : CWriteRef ctx .bit) :
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) →
      Store ctx → Store ctx × (foldProgram (oracles := oracles) (services := services)
        parity temporary pairs).Path
  | [], store => (store, ())
  | input :: rest, store => Circuit.sequenceStoreRecord (stepProgram parity temporary input)
      (foldProgram parity temporary rest) (stepRecord parity temporary input)
      (foldRecord parity temporary rest) store

/-- The complete path starts with the actual paid clear outcome. -/
def record (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) :
    Store ctx → Store ctx × (program (oracles := oracles) (services := services)
      parity temporary pairs).Path :=
  Circuit.sequenceStoreRecord (MaskParity.instruction (MaskParity.clearOp parity))
    (foldProgram parity temporary pairs) (MaskParity.instructionStep (MaskParity.clearOp parity))
    (foldRecord parity temporary pairs)

/-- The retained record's Store is exactly the chronological native pair fold. -/
lemma foldRecord_store (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) (store : Store ctx) :
    (foldRecord (oracles := oracles) (services := services) parity temporary pairs store).1 =
      foldStore parity temporary pairs store := by
  induction pairs generalizing store with
  | nil => rfl
  | cons input rest ih => exact ih (stepStore parity temporary input store)

/-- The same actual clear and pair records produce the proved Store update. -/
lemma record_store (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) (store : Store ctx) :
    (record (oracles := oracles) (services := services) parity temporary pairs store).1 =
      storeStep parity temporary pairs store :=
  foldRecord_store parity temporary pairs (store.applyOp (MaskParity.clearOp parity))

/-- Every actual intermediate Store is retained alongside arbitrary old histories and references. -/
lemma foldProgram_execute (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (foldProgram parity temporary pairs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := foldRecord (oracles := oracles) (services := services)
          parity temporary pairs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction pairs generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical environment Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons input rest ih =>
      exact Circuit.execute_sequenceStoreRecord _ _ environment
        (stepRecord parity temporary input) (foldRecord parity temporary rest)
        (stepProgram_execute parity temporary input environment)
        (fun reference history _ current => ih reference current) Reference state

/-- Actual runtime table parity is a closed native program on the full incoming state. -/
lemma program_execute (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (program parity temporary pairs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := record (oracles := oracles) (services := services)
          parity temporary pairs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceStoreRecord _ _ environment
    (MaskParity.instructionStep (MaskParity.clearOp parity)) (foldRecord parity temporary pairs)
    (instruction_execute _ environment) (foldProgram_execute parity temporary pairs environment)
    Reference state

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
