/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Latch
import all QuantumAlg.Core.Execution.Preparation.Observation

/-!
# The real initialized producer supplies its absent latch internally

The genuine retained allocations preserve reference weights. The actual XOR
clears the accepted bit independently of every earlier cell value, and real
quantum preparation preserves those same classical operands. No caller
provides an absent latch, selected payload or prepared quantum state.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The five real retained allocations preserve every constant full reference weight. -/
theorem Persistent.allocation_reference (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (coefficient : ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Persistent.allocation (model := executionModel input) base N).execute Reference state)
      (fun _ _ => coefficient) left right =
      ExecutionState.referenceFiberSum state (fun _ _ => coefficient) left right := by
  let first := Circuit.retain (model := executionModel input) base base.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh
  let second := Circuit.retain (model := executionModel input) (Persistent.resultContext base N)
    (Persistent.resultContext base N).canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N)))
    (Persistent.resultContext base N).canonicalFreshKey_fresh
  let third := Circuit.retain (model := executionModel input) (Persistent.candidateContext base N)
    (Persistent.candidateContext base N).canonicalFreshKey .bit
    (Persistent.candidateContext base N).canonicalFreshKey_fresh
  let fourth := Circuit.retain (model := executionModel input) (Persistent.acceptedContext base N)
    (Persistent.acceptedContext base N).canonicalFreshKey (.unsignedWord (modulusBits N))
    (Persistent.acceptedContext base N).canonicalFreshKey_fresh
  let fifth := Circuit.retain (model := executionModel input) (Persistent.selectedContext base N)
    (Persistent.selectedContext base N).canonicalFreshKey .bit
    (Persistent.selectedContext base N).canonicalFreshKey_fresh
  let state1 := first.execute Reference state
  let state2 := second.execute Reference state1
  let state3 := third.execute Reference state2
  let state4 := fourth.execute Reference state3
  have sequence0 := Circuit.referenceFiberSum_execute_seq first
    (second.seq (third.seq (fourth.seq fifth))) state (fun _ => coefficient) left right
  have sequence1 := Circuit.referenceFiberSum_execute_seq second
    (third.seq (fourth.seq fifth)) state1 (fun _ => coefficient) left right
  have sequence2 := Circuit.referenceFiberSum_execute_seq third
    (fourth.seq fifth) state2 (fun _ => coefficient) left right
  have sequence3 := Circuit.referenceFiberSum_execute_seq fourth fifth state3
    (fun _ => coefficient) left right
  have retained0 := Circuit.referenceFiberSum_execute_retain
    (gates := AlgorithmGate.model) (oracles := DeclaredSource.model (sourceBounds input)
      (phaseBits N)) (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    base.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
    base.canonicalFreshKey_fresh state (fun _ => coefficient) left right
  have retained1 := Circuit.referenceFiberSum_execute_retain
    (gates := AlgorithmGate.model) (oracles := DeclaredSource.model (sourceBounds input)
      (phaseBits N)) (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (Persistent.resultContext base N).canonicalFreshKey
    (.product .bit (.unsignedWord (modulusBits N)))
    (Persistent.resultContext base N).canonicalFreshKey_fresh state1
    (fun _ => coefficient) left right
  have retained2 := Circuit.referenceFiberSum_execute_retain
    (gates := AlgorithmGate.model) (oracles := DeclaredSource.model (sourceBounds input)
      (phaseBits N)) (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (Persistent.candidateContext base N).canonicalFreshKey .bit
    (Persistent.candidateContext base N).canonicalFreshKey_fresh state2
    (fun _ => coefficient) left right
  have retained3 := Circuit.referenceFiberSum_execute_retain
    (gates := AlgorithmGate.model) (oracles := DeclaredSource.model (sourceBounds input)
      (phaseBits N)) (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (Persistent.acceptedContext base N).canonicalFreshKey (.unsignedWord (modulusBits N))
    (Persistent.acceptedContext base N).canonicalFreshKey_fresh state3
    (fun _ => coefficient) left right
  have retained4 := Circuit.referenceFiberSum_execute_retain
    (gates := AlgorithmGate.model) (oracles := DeclaredSource.model (sourceBounds input)
      (phaseBits N)) (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (Persistent.selectedContext base N).canonicalFreshKey .bit
    (Persistent.selectedContext base N).canonicalFreshKey_fresh state4
    (fun _ => coefficient) left right
  exact sequence0.trans (sequence1.trans (sequence2.trans (sequence3.trans
    (retained4.trans (retained3.trans (retained2.trans (retained1.trans retained0)))))))

/-- The real clear supplies an absent latch in every complete weighted reference observation. -/
theorem Persistent.initialization_latch_reference (base : RuntimeCtx .quantum) (N : Nat)
    (input : Input N) {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Persistent.initialization (model := executionModel input) base N).execute Reference state)
      (fun entry _ => weight (NativeFactorScan.latchValue (Persistent.cells base N) entry.1))
      left right =
      ExecutionState.referenceFiberSum state (fun _ _ => weight .optionNone) left right := by
  let allocated := Persistent.allocation (model := executionModel input) base N
  let cleared := BitWord.instruction (execution := executionModel input)
    (NativeFactorScan.clearAcceptedOp (Persistent.cells base N))
  let initial := allocated.execute Reference state
  have sequence := Circuit.referenceFiberSum_execute_seq allocated cleared state
    (fun store => weight (NativeFactorScan.latchValue (Persistent.cells base N) store)) left right
  have clear :
      ExecutionState.referenceFiberSum (cleared.execute Reference initial)
        (fun entry _ => weight (NativeFactorScan.latchValue (Persistent.cells base N) entry.1))
        left right =
        ExecutionState.referenceFiberSum initial (fun _ _ => weight .optionNone) left right := by
    rw [show cleared = BitWord.instruction (execution := executionModel input)
      (NativeFactorScan.clearAcceptedOp (Persistent.cells base N)) from rfl,
      BitWord.bitWord_instruction_execute, ExecutionState.referenceFiberSum_mapClassical]
    apply congrArg (fun observe => ExecutionState.referenceFiberSum initial observe left right)
    funext entry basis
    exact congrArg weight (Persistent.cleared_latch base N entry.1)
  exact sequence.trans (clear.trans
    (Persistent.allocation_reference base N input state (weight .optionNone) left right))

/-- Actual persistent initialization and single-bank preparation provide the empty source fold. -/
theorem Initialized.ready_latch_reference (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Initialized.ready base noQuantum N input).execute Reference state)
      (fun entry _ => weight (NativeFactorScan.latchValue
        (Initialized.cells base noQuantum N) entry.1)) left right =
    ExecutionState.referenceFiberSum state (fun _ _ => weight .optionNone) left right := by
  let initial := Persistent.initialization (model := executionModel input) base N
  let prepared := Sampling.prepare (Persistent.context base N)
    (Initialized.noQuantumStorage base noQuantum N) N input
  have sequence := Circuit.referenceFiberSum_execute_seq initial prepared state
    (fun store => weight (NativeFactorScan.latchValue
      (Initialized.cells base noQuantum N) store)) left right
  have preparation := Circuit.referenceFiberSum_execute_prepareZero_input
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (latchInput (Persistent.context base N) N (Persistent.cells base N))
    (Persistent.context base N).canonicalFreshKey (layout N)
    (Persistent.context base N).canonicalFreshKey_fresh
    (allocationDisjoint (Persistent.context base N)
      (Initialized.noQuantumStorage base noQuantum N) N) (initial.execute Reference state)
    (fun value => weight (CShape.packOption value)) left right
  exact sequence.trans (preparation.trans
    (Persistent.initialization_latch_reference base N input state weight left right))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
