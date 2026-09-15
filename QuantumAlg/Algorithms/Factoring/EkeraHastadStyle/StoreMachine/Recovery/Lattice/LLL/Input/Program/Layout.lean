/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Reset.Run
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Program.Resources

/-!
# Original pair-to-LLL wiring and actual source conditions

The original sample, basis, target and reducer views refer to actual runtime
cells. Initial zeros are required only for basis cells and the third target
coordinate that the source-loading circuit deliberately leaves unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- The common raw-word width for the wide initialization and LLL driver. -/
abbrev Width (N : Nat) : Nat :=
  RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)

/-- Caller-owned references for the wide pair-to-LLL slice. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the initialization stage. -/
  initialization : LatticeFixedFuelInitializationMachine.Refs ctx N
  /-- Nested references for the target stage. -/
  target : LatticeWideTargetMachine.Refs ctx (shortLogBits N) (tradeoffBits N) (Width N)
  firstTargetK :
    target.first.k = LatticeLoading.writeInput initialization.pair.first.k
  secondTargetK :
    target.second.k = LatticeLoading.writeInput initialization.pair.second.k
  targetModulus :
    target.modulus = LatticeLoading.writeInput initialization.raw.b21
  targetPoint :
    target.target.point =
      LatticeRepresentation.targetRefs initialization.raw initialization.roles

/-- The prefix view of the caller-owned initialization references. -/
def prefixRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : LatticeWideInitializationPrefix.Refs ctx N where
  pair := refs.initialization.pair
  raw := refs.initialization.raw
  roles := refs.initialization.roles

/-- A read that avoids every key written by the decoder--basis prefix. -/
def AvoidsPrefixWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    {shape : CShape} (input : CInputRef ctx shape) (refs : Refs ctx N) : Prop :=
  ∀ key ∈ LatticeWideInitializationPrefix.writtenKeys (prefixRefs refs),
    key ∉ input.storageKeys

/-- A read that avoids every mutable cell of the wide target loader. -/
def AvoidsTargetWrites {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {m ell width : Nat} {shape : CShape} (input : CInputRef ctx shape)
    (refs : LatticeWideTargetMachine.Refs ctx m ell width) : Prop :=
  refs.first.scaled.key ∉ input.storageKeys ∧
    refs.second.scaled.key ∉ input.storageKeys ∧
      refs.target.first.scratch.key ∉ input.storageKeys ∧
        refs.target.first.isZero.key ∉ input.storageKeys ∧
          refs.target.first.belowHalf.key ∉ input.storageKeys ∧
            refs.target.first.output.key ∉ input.storageKeys ∧
              refs.target.second.scratch.key ∉ input.storageKeys ∧
                refs.target.second.isZero.key ∉ input.storageKeys ∧
                  refs.target.second.belowHalf.key ∉ input.storageKeys ∧
                    refs.target.second.output.key ∉ input.storageKeys

/-- A caller read outside the decoder--basis prefix and wide target loader writes. -/
def DecodeTargetCallerSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  AvoidsPrefixWrites other refs ∧ AvoidsTargetWrites other refs.target

/-- Local separation certificates for each real instruction package. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  prefixSeparation : LatticeWideInitializationPrefix.Separation (prefixRefs refs)
  target : LatticeWideTargetMachine.Separation refs.target
  metric : LatticeMetricMachine.Separation refs.initialization.driver.machine.basis
    refs.initialization.driver.metric
  reset : refs.initialization.driver.machine.Separated
  driver : LatticeFixedFuelMachine.Separation refs.initialization.driver
  firstScratchAvoidsPrefix :
    AvoidsPrefixWrites
      (LatticeTarget.writeInput refs.target.target.first.scratch) refs
  secondScratchAvoidsPrefix :
    AvoidsPrefixWrites
      (LatticeTarget.writeInput refs.target.target.second.scratch) refs
  targetThirdAvoidsPrefix :
    AvoidsPrefixWrites
      (LatticeState.coordinateInput refs.target.target.point.third) refs
  driverBasisAvoidsTarget : ∀ cell : LatticeMetricMachine.BasisCell,
    AvoidsTargetWrites
      (LatticeMetricMachine.basisCellInput refs.initialization.driver.machine.basis cell)
      refs.target

/-- A complete original caller read frame through decoding, target loading and the LLL driver. -/
structure CallerSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop where
  decodeTarget : DecodeTargetCallerSeparated refs other
  fixedFuel : LatticeFixedFuelMachine.CallerSeparated refs.initialization.driver other

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The two original samples selected by the actual terminal measurement cells. -/
def sourceSamples (refs : Refs ctx N) (store : Store ctx) :
    RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) :=
  LatticeWideInitializationPrefix.sourceSamples (prefixRefs refs) store

/-- The independent pure source basis from the original actual terminal samples. -/
def sourceBasis (refs : Refs ctx N) (store : Store ctx) : NumberTheory.IntegerBasis3 :=
  RSA.shortLogLatticeBasis (shortLogBits N) (tradeoffBits N) (sourceSamples refs store)

/-- Only the unmodified third target coordinate needs an original initial zero. -/
def TargetInitialZero (store : Store ctx) (refs : Refs ctx N) : Prop :=
  RawSignedRepresents (store.read (LatticeState.coordinateInput refs.target.target.point.third)) 0

/-- Initial zeros are limited to the four unmodified basis cells and the third target coordinate. -/
def InitialConditions (store : Store ctx) (refs : Refs ctx N) : Prop :=
  LatticeWideInitializationPrefix.BasisInitialZero store (prefixRefs refs) ∧
    TargetInitialZero store refs

/-- The independent mathematical LLL state immediately before its actual driver begins. -/
def initialState (refs : Refs ctx N) (store : Store ctx) : NumberTheory.LLLState3 :=
  LatticeFixedFuelMachine.initialState (sourceBasis refs store)

/-- Every original source basis is full rank independently of incoming scratch values. -/
theorem sourceBasis_fullRank (refs : Refs ctx N) (store : Store ctx) :
    (sourceBasis refs store).FullRank := RSA.shortLogLatticeBasis_fullRank _ _ _

/-- The mathematical initial state is bounded by its own original source basis. -/
theorem initialState_bounded (refs : Refs ctx N) (store : Store ctx) :
    (initialState refs store).BoundedFrom (sourceBasis refs store) :=
  NumberTheory.LLLState3.boundedFrom_initial _ (sourceBasis_fullRank refs store)

/-- The original common width meets the source-dependent LLL capacity requirement. -/
theorem initialState_capacity (refs : Refs ctx N) (store : Store ctx) :
    Nat.size (256 * (NumberTheory.lllStateEnvelope3 (sourceBasis refs store) + 1) ^ 8) +
      1 ≤ Width N :=
  LatticeFixedFuelInitializationMachine.sourceBasis_capacity refs.initialization store

/-- The original pure source basis meets every actual first-step scalar range requirement. -/
theorem initialState_stepFits (refs : Refs ctx N) (store : Store ctx) :
    LatticeStepBounds.StepFits (Width N) (sourceBasis refs store) :=
  LatticeStepBounds.shortLog_initial_stepFits N (shortLogBits N)
    (tradeoffBits N) (sourceSamples refs store)

/-- The unchanged mathematical result at the original prescribed public recovery fuel. -/
def finalState (refs : Refs ctx N) (store : Store ctx) : NumberTheory.LLLState3 :=
  NumberTheory.lllRun3 (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
    (initialState refs store)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
