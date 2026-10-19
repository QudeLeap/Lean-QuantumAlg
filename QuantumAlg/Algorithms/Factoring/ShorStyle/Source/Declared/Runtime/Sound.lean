/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Admission
import all QuantumAlg.Core.Execution.Input.Successor.Distribution
import all QuantumAlg.Core.Execution.Basis.Seeded.Admission
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Recovery

/-!
# Actual initializer and complete feedback supply independent latch admission

The accepted local domain permits an absent latch or a declared factor. The
original initializer supplies absence, and complete native recovery preserves
soundness for every positive actual record. Local successor admission is
transported through the genuine next input, retaining its store and service.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A present persistent result must be one of the original problem's declared factors. -/
def SoundLatch {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (value : CShape.Value (.option (.unsignedWord (modulusBits N)))) : Prop :=
  Probability.ReturnedDeclaredFactor model value ∨ value = .optionNone

private lemma firstPresent_sound {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (earlier later : CShape.Value (.option (.unsignedWord (modulusBits N))))
    (oldSound : SoundLatch model earlier) (newSound : SoundLatch model later) :
    SoundLatch model (NativeFactorScan.firstPresent earlier later) := by
  cases earlier with
  | optionNone => exact newSound
  | optionSome _ => exact oldSound

private lemma sourceWeight_zero {N : Nat} (input : Input N)
    (weight : SourceOutcome N → ℂ) (zero : ∀ outcome, weight outcome = 0) :
    SourceWeights.one input weight = 0 := by
  simp only [SourceWeights.one, zero, zero_mul, Finset.sum_const_zero, mul_zero]

/-- Actual complete recovery, feedback and reset preserve every positive latch record's domain. -/
lemma Completion.supported_sound (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (admitted : ∀ record, 0 < (state.block record).mass →
      SoundLatch model (NativeFactorScan.latchValue cells record.1))
    (record : Store (Iteration.context ctx N) ×
      ((executionModel N).HiddenState ×
        (History × (Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
          sameWires cells result).Path)))
    (positive : 0 < (((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result).execute
        (environment (Probability.Input.ofSemiprimeModel model)) Reference state).block
          record).mass) :
    SoundLatch model (NativeFactorScan.latchValue (Completion.cells ctx N cells) record.1) := by
  classical
  let input := Probability.Input.ofSemiprimeModel model
  let actual := (Completion.code ctx N input sameWires cells result).execute
    (environment (Probability.Input.ofSemiprimeModel model)) Reference state
  let bad := fun value => if SoundLatch model value then (0 : ℂ) else 1
  apply ExecutionState.supported_of_reference_zero actual
    (fun entry => SoundLatch model
      (NativeFactorScan.latchValue (Completion.cells ctx N cells) entry.1)) _ record positive
  intro left right
  have law := completion_latch_reference ctx N input sameWires cells result separated
    state seeded normalized bad left right
  refine law.trans ?_
  have matching (entry) (present : 0 < (state.block entry).mass)
      (_basis : ctx.register.Index) :
      SourceWeights.one input (fun outcome => bad
        (NativeFactorScan.firstPresent (NativeFactorScan.latchValue cells entry.1)
          (NativeFactorScan.sourceResult input outcome))) = 0 := by
    apply sourceWeight_zero
    intro outcome
    have sound := firstPresent_sound model _ _ (admitted entry present)
      (NativeFactorScan.sourceResult_declared_or_none model outcome)
    simp only [bad, sound, if_true]
  have same := ExecutionState.referenceFiberSum_congr_on_positive state _ (fun _ _ => 0)
    matching left right
  refine same.trans ?_
  simp only [ExecutionState.referenceFiberSum, zero_mul, Finset.sum_const_zero]

/-- The genuine initializer supplies absence in every positive local successor record. -/
lemma Initialized.nextInput_latch_absent (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat)
    {environment : (executionModel N).Environment} {Reference : Register}
    (original : OracleInput (executionModel N).classicalOracles base Reference)
    (record : Store (Initialized.bank base noQuantum N) × (executionModel N).HiddenState)
    (positive : 0 < (((Initialized.ready base noQuantum N).nextInput
      environment original).localState.block record).mass) :
    NativeFactorScan.latchValue (Initialized.cells base noQuantum N) record.1 = .optionNone := by
  let code := Initialized.ready base noQuantum N
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))
  obtain ⟨actualRecord, sameStore, _sameService, present⟩ :=
    Circuit.nextInput_local_supported_execution
      (environment := environment) code original record positive
  have absent : NativeFactorScan.latchValue (Initialized.cells base noQuantum N)
      actualRecord.1 = .optionNone := by
    apply ExecutionState.supported_of_reference_zero (code.execute environment Reference entered)
      (fun entry => NativeFactorScan.latchValue (Initialized.cells base noQuantum N)
        entry.1 = .optionNone) _ actualRecord present
    intro left right
    refine (Initialized.ready_latch_reference (environment := environment) base noQuantum N entered
      (fun value => if value = .optionNone then (0 : ℂ) else 1) left right).trans ?_
    simp only [if_true, ExecutionState.referenceFiberSum, zero_mul, Finset.sum_const_zero]
  simpa only [sameStore] using absent

/-- A genuine complete successor preserves local soundness for every reference extension. -/
lemma Completion.nextInput_latch_sound (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles ctx Reference)
    (localSeed : ∀ (entry : Store ctx ×
        (executionModel N).HiddenState)
      (basis : ctx.register.Index), basis ≠ ctx.quantumLayout.zeroLabel →
        (original.localState.block entry).matrix basis basis = 0)
    (localSound : ∀ entry, 0 < (original.localState.block entry).mass →
      SoundLatch model (NativeFactorScan.latchValue cells entry.1))
    (record : Store (Iteration.context ctx N) ×
      (executionModel N).HiddenState)
    (positive : 0 < (((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result).nextInput
        (environment (Probability.Input.ofSemiprimeModel model)) original).localState.block
          record).mass) :
    SoundLatch model (NativeFactorScan.latchValue (Completion.cells ctx N cells) record.1) := by
  let input := Probability.Input.ofSemiprimeModel model
  let code := Completion.code ctx N input sameWires cells result
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))
  have seeded := BasisSeeded.oracleInput_of_local_support (model := executionModel N)
    ctx.quantumLayout.zeroLabel original localSeed
  have enteredSeeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel entered :=
    BasisSeeded.mapStore ctx.quantumLayout.zeroLabel original.state seeded id
      (fun entry => (entry.2, ()))
  have enteredSound : ∀ entry, 0 < (entered.block entry).mass →
      SoundLatch model (NativeFactorScan.latchValue cells entry.1) := by
    intro entry present
    obtain ⟨previous, same, previousPositive⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff original.state
        (fun entry => (entry.1, (entry.2, ()))) entry).mp present
    have localPositive : 0 < (original.localState.block previous).mass := by
      simpa only [OracleInput.oracleInput_localState_block, DensityOperator.marginalLeft_mass]
        using previousPositive
    have sameStore : previous.1 = entry.1 := congrArg Prod.fst same
    simpa only [sameStore] using localSound previous localPositive
  obtain ⟨actualRecord, sameStore, _sameService, present⟩ :=
    Circuit.nextInput_local_supported_execution
      (environment := environment (Probability.Input.ofSemiprimeModel model))
      code original record positive
  have sound := Completion.supported_sound ctx model sameWires cells result separated
    entered enteredSeeded
    (original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, ())))) enteredSound actualRecord present
  simpa only [sameStore] using sound

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
