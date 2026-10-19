/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout

/-!
# Actual pair decoding, target loading, initialization and fixed-fuel LLL

The original order is decode and load basis, load target, refresh the Gram
snapshot and reset the phase, then execute the public fixed fuel. The target
is loaded before the Gram refresh because their original scratch cells may alias.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Decode the actual original samples and source basis before loading the actual target. -/
def decodeTargetInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (LatticeWideInitializationPrefix.decodeBasisInto (prefixRefs refs))
    (LatticeWideTargetMachine.loadTargetInto refs.target)

/-- The actual chronological stores and complete native paths of this composition. -/
def decodeTargetStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (decodeTargetInto refs).Path :=
  let first := LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store
  let second := LatticeWideTargetMachine.targetStep refs.target first.1
  (second.1, (first.2, second.2))

/-- The actual composed execution retains every incoming state block and original history. -/
lemma decodeTargetInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodeTargetInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := decodeTargetStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeWideInitializationPrefix.decodeBasisInto (prefixRefs refs))
    (LatticeWideTargetMachine.loadTargetInto refs.target)
    (fun before =>
      let actual := LatticeWideInitializationPrefix.decodeBasisStep (model := model)
        (prefixRefs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeWideTargetMachine.targetStep (model := model) refs.target before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeWideInitializationPrefix.decodeBasisInto_execute (prefixRefs refs)
        reference current)
    (fun reference _history _ current =>
      LatticeWideTargetMachine.loadTargetInto_execute refs.target reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Load the original actual basis and target before refreshing Gram data and resetting phase. -/
def initializeWideInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (decodeTargetInto refs)
    (LatticeFixedFuelMachine.refreshResetInto refs.initialization.driver)

/-- The actual chronological stores and complete native paths of this composition. -/
def initializeWideStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (initializeWideInto refs).Path :=
  let first := decodeTargetStep refs store
  let second := LatticeFixedFuelMachine.refreshResetStep refs.initialization.driver first.1
  (second.1, (first.2, second.2))

/-- The actual composed execution retains every incoming state block and original history. -/
lemma initializeWideInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (initializeWideInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := initializeWideStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (decodeTargetInto refs)
    (LatticeFixedFuelMachine.refreshResetInto refs.initialization.driver)
    (fun before =>
      let actual := decodeTargetStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeFixedFuelMachine.refreshResetStep (model := model)
        refs.initialization.driver before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => decodeTargetInto_execute refs reference current)
    (fun reference _history _ current =>
      LatticeFixedFuelMachine.refreshResetInto_execute refs.initialization.driver
        reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Execute original sample and target loading before the original initialized fixed-fuel LLL. -/
def pairToLllInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (decodeTargetInto refs)
    (LatticeFixedFuelMachine.initializedInto (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver)

/-- The actual chronological stores and complete native paths of this composition. -/
def pairToLllStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairToLllInto refs).Path :=
  let first := decodeTargetStep refs store
  let second := LatticeFixedFuelMachine.initializedStep (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver first.1
  (second.1, (first.2, second.2))

/-- The actual composed execution retains every incoming state block and original history. -/
lemma pairToLllInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairToLllInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := pairToLllStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (decodeTargetInto refs)
    (LatticeFixedFuelMachine.initializedInto (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver)
    (fun before =>
      let actual := decodeTargetStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeFixedFuelMachine.initializedStep (model := model)
        (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
        refs.initialization.driver before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => decodeTargetInto_execute refs reference current)
    (fun reference _history _ current =>
      LatticeFixedFuelMachine.initializedInto_execute
        (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
        refs.initialization.driver reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
