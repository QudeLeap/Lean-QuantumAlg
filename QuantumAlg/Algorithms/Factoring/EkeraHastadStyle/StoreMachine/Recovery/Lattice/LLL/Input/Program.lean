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

/-- Decode the actual original samples and source basis before loading the actual target. -/
def decodeTargetInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticeWideInitializationPrefix.decodeBasisInto (prefixRefs refs))
    (LatticeWideTargetMachine.loadTargetInto refs.target)

/-- The actual chronological stores and complete native paths of this composition. -/
def decodeTargetStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (decodeTargetInto refs).Path :=
  let first := LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store
  let second := LatticeWideTargetMachine.targetStep refs.target first.1
  (second.1, (first.2, second.2))

/-- The actual composed execution retains every incoming state block and original history. -/
theorem decodeTargetInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decodeTargetInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((decodeTargetStep refs entry.1).1, (entry.2, (decodeTargetStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeWideInitializationPrefix.decodeBasisInto (prefixRefs refs))
    (LatticeWideTargetMachine.loadTargetInto refs.target)
    (LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs))
    (LatticeWideTargetMachine.targetStep refs.target)
    (LatticeWideInitializationPrefix.decodeBasisInto_execute (prefixRefs refs))
    (LatticeWideTargetMachine.loadTargetInto_execute refs.target) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Load the original actual basis and target before refreshing Gram data and resetting phase. -/
def initializeWideInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (decodeTargetInto refs)
    (LatticeFixedFuelMachine.refreshResetInto refs.initialization.driver)

/-- The actual chronological stores and complete native paths of this composition. -/
def initializeWideStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (initializeWideInto refs).Path :=
  let first := decodeTargetStep refs store
  let second := LatticeFixedFuelMachine.refreshResetStep refs.initialization.driver first.1
  (second.1, (first.2, second.2))

/-- The actual composed execution retains every incoming state block and original history. -/
theorem initializeWideInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializeWideInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((initializeWideStep refs entry.1).1, (entry.2, (initializeWideStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (decodeTargetInto refs)
    (LatticeFixedFuelMachine.refreshResetInto refs.initialization.driver)
    (decodeTargetStep refs)
    (LatticeFixedFuelMachine.refreshResetStep refs.initialization.driver)
    (decodeTargetInto_execute refs)
    (LatticeFixedFuelMachine.refreshResetInto_execute refs.initialization.driver)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Execute original sample and target loading before the original initialized fixed-fuel LLL. -/
def pairToLllInto (refs : Refs ctx N) : Circuit ctx ctx :=
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
theorem pairToLllInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairToLllInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((pairToLllStep refs entry.1).1, (entry.2, (pairToLllStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (decodeTargetInto refs)
    (LatticeFixedFuelMachine.initializedInto (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver)
    (decodeTargetStep refs)
    (LatticeFixedFuelMachine.initializedStep (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver)
    (decodeTargetInto_execute refs)
    (LatticeFixedFuelMachine.initializedInto_execute (RSA.shortLogRecoveryFuel
      (shortLogBits N) (tradeoffBits N)) refs.initialization.driver) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
