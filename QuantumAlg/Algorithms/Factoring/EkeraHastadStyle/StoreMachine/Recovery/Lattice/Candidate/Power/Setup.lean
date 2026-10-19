/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Layout

/-!
# Actual shared modular setup from the retained sampler parameter
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual nominal packing of the original raw parameter base. -/
def packOp (refs : Refs ctx N) :
    ClassicalOp (.unsignedWord (modulusBits N)) (.canonicalResidue (modulusBits N)) ctx ctx :=
  .packCanonicalResidue (modulusBits N) ctx (parameterBaseInput refs) refs.generator

/-- Width-many literal native shifts materialize the original public modulus. -/
def modulusInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  ClassicalRoutines.ConstantWord.circuit refs.modulus N

/-- The original public target exponent is materialized by actual width-many native shifts. -/
def exponentInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  ClassicalRoutines.ConstantWord.circuit refs.targetExponent (RSA.targetExponent N)

/-- Actual shared modulus initialization and its complete store and instruction path. -/
def modulusStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (modulusInto refs).Path :=
  ClassicalRoutines.ConstantWord.foldStep refs.modulus
    (List.ofFn (ClassicalRoutines.ConstantWord.constantBits (modulusBits N + 1) N)) store

/-- Actual target exponent initialization and its complete store and instruction path. -/
def exponentStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (exponentInto refs).Path :=
  ClassicalRoutines.ConstantWord.foldStep refs.targetExponent
    (List.ofFn (ClassicalRoutines.ConstantWord.constantBits (modulusBits N) (RSA.targetExponent N)))
    store

/-- Actual base packing precedes original modulus and exponent materialization. -/
def prepareInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (packOp refs))
    (.seq (modulusInto refs) (exponentInto refs))

/-- The actual three chronological shared-input updates and paths. -/
def prepareStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (prepareInto refs).Path :=
  let packed := BitWord.instructionStep (execution := model) (packOp refs) store
  let loaded := modulusStep refs packed.1
  let exponent := exponentStep refs loaded.1
  (exponent.1, (packed.2, (loaded.2, exponent.2)))

/-- Actual shared target powering reads the real initialized generator and target exponent. -/
def powerInto (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  ClassicalRoutines.Modular.NativePower.into (modulusSpec input)
    (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower

/-- Complete actual target-power result and selected exponent-bit paths. -/
def powerStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (powerInto input refs).Path :=
  ClassicalRoutines.Modular.NativePower.intoStep (modulusSpec input)
    (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower store

/-- Initialize original shared inputs and execute actual target powering before candidate
scanning. -/
def setupInto (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (prepareInto refs) (powerInto input refs)

/-- Complete actual shared setup state and all four chronological component paths. -/
def setupStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (setupInto input refs).Path :=
  let prepared := prepareStep refs store
  let powered := powerStep input refs prepared.1
  (powered.1, (prepared.2, powered.2))

private lemma modulusExponent_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (modulusInto refs) (exponentInto refs)).execute environment Reference state =
      state.mapClassical (fun entry =>
        let loaded := modulusStep refs entry.1
        let exponent := exponentStep refs loaded.1
        (exponent.1, (entry.2.1, (entry.2.2, (loaded.2, exponent.2))))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (modulusInto refs) (exponentInto refs)
    (fun before =>
      let actual := modulusStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := exponentStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      ClassicalRoutines.ConstantWord.constantWord_fold_execute refs.modulus _
        reference current)
    (fun reference _history _ current =>
      ClassicalRoutines.ConstantWord.constantWord_fold_execute refs.targetExponent _
        reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual base packing and constant materialization retain all incoming histories and
references. -/
lemma prepareInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prepareInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := prepareStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (packOp refs))
    (.seq (modulusInto refs) (exponentInto refs))
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (packOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let loaded := modulusStep refs before.1
      let exponent := exponentStep refs loaded.1
      ((exponent.1, before.2), (loaded.2, exponent.2)))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute
      (environment := environment) _ current)
    (fun reference _history _ current =>
      (modulusExponent_execute refs reference current).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl))
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual full interpreter connects the retained base, initialized constants and target
power. -/
lemma setupInto_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (setupInto input refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := setupStep input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (prepareInto refs) (powerInto input refs)
    (fun before =>
      let actual := prepareStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := powerStep input refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => prepareInto_execute refs reference current)
    (fun reference _history _ current =>
      ClassicalRoutines.Modular.NativePower.nativePower_into_execute (modulusSpec input)
        (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower
        reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
