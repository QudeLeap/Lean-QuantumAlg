/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity

/-!
# Complete records of the actual classical mask-parity program

The native XOR leaves retain their actual computed outcomes. Their sequential
record uses each real intermediate Store and leaves every incoming history,
hidden service state and arbitrary quantum reference correlated as before.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

/-- The native result and actual write of this allocation-free instruction. -/
def instructionStep {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (store : Store ctx) : Store ctx × (instruction (oracles := oracles)
      (services := services) op).Path :=
  (store.applyOp op, op.eval (store.read op.inputRef))

private lemma instruction_execute {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (instruction op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := instructionStep (oracles := oracles) (services := services) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_classical_mapClassical environment (BitWord.application op) op.eval
    (BitWord.bitWord_application_evaluate op) Reference state

/-- The exact real chronological paths and caller stores of the selected-bit XOR fold. -/
def foldRecord (parity : CWriteRef ctx .bit) : (inputs : List (CInputRef ctx .bit)) →
    Store ctx → Store ctx × (foldProgram (oracles := oracles) (services := services)
      parity inputs).Path
  | [], store => (store, ())
  | input :: rest, store =>
      Circuit.sequenceStoreRecord (instruction (xorOp parity input)) (foldProgram parity rest)
        (instructionStep (xorOp parity input)) (foldRecord parity rest) store

/-- The record starts with the actual clear outcome and retains every subsequent XOR outcome. -/
def record (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (store : Store ctx) :
    Store ctx × (program (oracles := oracles) (services := services) parity inputs).Path :=
  Circuit.sequenceStoreRecord (instruction (clearOp parity)) (foldProgram parity inputs)
    (instructionStep (clearOp parity)) (foldRecord parity inputs) store

/-- The record's final store is exactly the chronological update proved to contain parity. -/
lemma foldRecord_store (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (store : Store ctx) :
    (foldRecord (oracles := oracles) (services := services) parity inputs store).1 =
      foldStore parity inputs store := by
  induction inputs generalizing store with
  | nil => rfl
  | cons input rest ih => exact ih (store.applyOp (xorOp parity input))

/-- The actual full record and the proved parity Store update have the same final Store. -/
lemma record_store (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (store : Store ctx) :
    (record (oracles := oracles) (services := services) parity inputs store).1 =
      storeStep parity inputs store :=
  foldRecord_store parity inputs (store.applyOp (clearOp parity))

/-- Each real XOR is interpreted on its actual intermediate Store, reference and history. -/
lemma foldProgram_execute (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (foldProgram parity inputs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := foldRecord (oracles := oracles) (services := services) parity inputs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction inputs generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical environment Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons input rest ih =>
      exact Circuit.execute_sequenceStoreRecord _ _ environment
        (instructionStep (xorOp parity input)) (foldRecord parity rest)
        (instruction_execute (xorOp parity input) environment)
        (fun reference history _ current => ih reference current) Reference state

/-- The whole paid clear/fold has its exact deterministic action on arbitrary joint input. -/
lemma program_execute (parity : CWriteRef ctx .bit) (inputs : List (CInputRef ctx .bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (program parity inputs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := record (oracles := oracles) (services := services) parity inputs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceStoreRecord _ _ environment
    (instructionStep (clearOp parity)) (foldRecord parity inputs)
    (instruction_execute (clearOp parity) environment)
    (foldProgram_execute parity inputs environment) Reference state

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
