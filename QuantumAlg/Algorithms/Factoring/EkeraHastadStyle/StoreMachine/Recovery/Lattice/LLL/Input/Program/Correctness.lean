/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Decode

/-!
# Actual source-to-LLL initialization and fixed-fuel correctness

The loaded actual source basis establishes the complete original LLL invariant
when Gram data and phase are initialized. The subsequent actual fixed-fuel run
realizes the unchanged mathematical run at the prescribed public recovery fuel.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual loading, Gram refresh and phase reset establish the complete original LLL invariant. -/
lemma initializeWideInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeFixedFuelMachine.StoreInvariant refs.initialization.driver (sourceBasis refs store)
      (initializeWideStep refs store).1 (initialState refs store) :=
  LatticeFixedFuelMachine.refreshResetInto_correct refs.initialization.driver separation.driver
    (decodeTargetStep refs store).1 (sourceBasis refs store)
    (decodeTargetInto_basis refs separation store initial.1)
    (sourceBasis_fullRank refs store) (initialState_capacity refs store)

/-- Actual initialization retains the complete caller frame independently of initial values. -/
lemma initializeWideInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (initializeWideStep refs store).1.read other = store.read other :=
  (LatticeFixedFuelMachine.refreshResetInto_callerFrame refs.initialization.driver _ other
    separate.fixedFuel).trans (decodeTargetInto_callerFrame refs store other separate.decodeTarget)

/-- The actual source-to-LLL run realizes the original mathematical result at its original fuel. -/
lemma pairToLllInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeFixedFuelMachine.StoreInvariant refs.initialization.driver (sourceBasis refs store)
      (pairToLllStep refs store).1 (finalState refs store) :=
  LatticeFixedFuelMachine.initializedInto_correct
    (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
    refs.initialization.driver separation.driver (decodeTargetStep refs store).1
    (sourceBasis refs store) (decodeTargetInto_basis refs separation store initial.1)
    (sourceBasis_fullRank refs store) (initialState_capacity refs store)

/-- Reads outside the original source-loader and LLL writes survive the complete actual run. -/
lemma pairToLllInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (pairToLllStep refs store).1.read other = store.read other :=
  (LatticeFixedFuelMachine.initializedInto_callerFrame
    (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) refs.initialization.driver _
    other separate.fixedFuel).trans
    (decodeTargetInto_callerFrame refs store other separate.decodeTarget)

/-- The final mathematical basis is the output of the original public short-log recovery trace. -/
lemma finalState_basis_eq_shortLogRecoveryTrace_output (refs : Refs ctx N) (store : Store ctx) :
    (finalState refs store).basis =
      (RSA.shortLogRecoveryTrace (shortLogBits N) (tradeoffBits N)
        (sourceSamples refs store)).output := by
  unfold finalState initialState sourceBasis LatticeFixedFuelMachine.initialState
  rw [RSA.shortLogRecoveryTrace]
  exact (NumberTheory.lllReduce3WithFuel_output_eq_finalBasis _ _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
