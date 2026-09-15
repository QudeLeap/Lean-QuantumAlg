/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Correctness
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Full joint state at the actual first-success factor output

Actual retained selection groups the original factor-vector blocks. Their
common restored bank seed and complete incoming reference survive this
grouping, for both populated and empty outputs. The independent requirement
selects every live quantum wire and conditions on the actual factor cell.
Borrowed classical-reference restoration remains a separate obligation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] NativeRetryChain.context NativeRetryChain.code
  ShortDLP.CompiledMAU.RuntimeResults.context ExecutionState.referenceFiberSum

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The independent target retains the original bank seed and the complete input reference. -/
def stateTarget {Reference : Register} (input : Execution.Input base Reference) :
    DensityOperator (Register.prod
      (context (NativeRetryChain.context base noQuantum N count) N).register Reference) :=
  BasisReference.target (NativeRetryChain.restoredSeed base noQuantum N count)
    input.state.referenceMarginal

/-- The independent full joint target is normalized for every actual normalized input. -/
theorem stateTarget_normalized {Reference : Register} (input : Execution.Input base Reference) :
    (stateTarget base noQuantum N count input).IsNormalized :=
  BasisReference.target_normalized (NativeRetryChain.restoredSeed base noQuantum N count)
    input.state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized)

private theorem mixed_transport {R : Register}
    (firstTarget secondTarget firstBlock secondBlock : DensityOperator R)
    (firstNormalized : firstTarget.IsNormalized) (secondNormalized : secondTarget.IsNormalized)
    (sameTarget : firstTarget = secondTarget) (sameBlock : firstBlock = secondBlock)
    (holds : (StatePromise.mixed firstTarget firstNormalized).Holds firstBlock) :
    (StatePromise.mixed secondTarget secondNormalized).Holds secondBlock := by
  cases sameTarget
  cases sameBlock
  exact holds

private theorem chain_statePromise (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference)
    (value : (CShape.fixedVector (count + 1)
      (LatticeBatchRecoveryOutput.OutputShape N)).Value) :
    (StatePromise.mixed (stateTarget base noQuantum N count input)
      (stateTarget_normalized base noQuantum N count input)).Holds
        ((ExecutionState.mapClassical
          ((NativeRetryChain.run base noQuantum specification count).execute Reference input.state)
          (NativeRetryChain.run base noQuantum specification count).result).block value) := by
  let entered : State base Reference (Store base) :=
    input.state.mapClassical (fun store => (store, store))
  have referenceSame : entered.referenceMarginal = input.state.referenceMarginal := by
    exact congrArg (fun density : DensityOperator (Register.prod base.register Reference) =>
      DensityOperator.marginalLeft (density.reindex
        (S := Register.prod Reference base.register)
        (Equiv.prodComm base.register.Index Reference.Index)))
      (ExecutionState.mapClassical_quantumMarginal input.state (fun store => (store, store)))
  let program := NativeRetryChain.run base noQuantum specification count
  have enter : program.execute Reference input.state =
      (NativeRetryChain.code base noQuantum specification count).execute Reference entered := by
    unfold AlgorithmRun.execute
    apply congrArg (fun state : State base Reference (Store base) =>
      (NativeRetryChain.code base noQuantum specification count).execute Reference state)
    congr 1
  have readout := congrArg
    (fun final : ExecutionState program.Record
        ((NativeRetryChain.context base noQuantum N count).register.prod Reference) =>
      (final.mapClassical program.result).block value) enter
  have actual := NativeRetryChain.output_statePromise base noQuantum N count specification
    entered ((input.state.mapClassical_mass _).trans input.normalized) value
  have targetSame :
      BasisReference.target (NativeRetryChain.restoredSeed base noQuantum N count)
        entered.referenceMarginal = stateTarget base noQuantum N count input :=
    congrArg (BasisReference.target (NativeRetryChain.restoredSeed base noQuantum N count))
      referenceSame
  exact mixed_transport _ _ _ _ _ _ targetSame readout.symm actual


/-- The actual selected output state is the original complete vector state grouped by selection. -/
theorem outputState_eq_selection (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum specification count).finalState Reference input.state).mapClassical
        (run base noQuantum specification count).output.eval =
      ExecutionState.mapClassical
        (ExecutionState.mapClassical
          ((NativeRetryChain.run base noQuantum specification count).execute Reference input.state)
          (NativeRetryChain.run base noQuantum specification count).result)
        (firstValue (N := N)) := by
  let sampling := NativeRetryChain.run base noQuantum specification count
  let sampled := sampling.execute Reference input.state
  have actual := congrArg
    (fun state : ExecutionState (run base noQuantum specification count).Record
        (Register.prod (context (NativeRetryChain.context base noQuantum N count) N).register
          Reference) => state.mapClassical (run base noQuantum specification count).result)
    (run_execute base noQuantum specification count Reference input.state)
  have projected : (run base noQuantum specification count).result ∘
      selectionRecord base noQuantum specification count =
        firstValue ∘ (NativeRetryChain.run base noQuantum specification count).result := by
    funext record
    exact run_output base noQuantum specification count record.1
  have recovered := ExecutionState.executionState_mapClassical_comp sampled
    (selectionRecord base noQuantum specification count)
    (run base noQuantum specification count).result
  have grouped := ExecutionState.executionState_mapClassical_comp sampled
    sampling.result (firstValue (N := N))
  have projectedMap := congrArg (fun read => sampled.mapClassical read) projected
  exact (AlgorithmRun.finalState_readout (run base noQuantum specification count)
    Reference input.state).trans
      (actual.trans (recovered.trans (projectedMap.trans grouped.symm)))

/-- Every actual factor block retains the same complete bank-reference target, including failure. -/
theorem output_statePromise (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed (stateTarget base noQuantum N count input)
      (stateTarget_normalized base noQuantum N count input)).Holds
      ((((run base noQuantum specification count).finalState Reference input.state).mapClassical
        (run base noQuantum specification count).output.eval).block value) := by
  rw [outputState_eq_selection]
  exact ExecutionState.mapClassical_mixed _ (firstValue (N := N))
    (stateTarget base noQuantum N count input) (stateTarget_normalized base noQuantum N count input)
    (chain_statePromise base noQuantum N count specification input) value

/-- Every live quantum wire and the full reference are promised at the actual selected cell. -/
def stateRequirement :
    StateRequirement base (context (NativeRetryChain.context base noQuantum N count) N) :=
  .jointReference Finset.univ
    (.read (.storage (resultRef (NativeRetryChain.context base noQuantum N count) N).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (context (NativeRetryChain.context base noQuantum N count) N).quantumLayout
        Finset.univ Reference (stateTarget base noQuantum N count input))
      ((DensityOperator.observeSelectionWithReference_mass
        (context (NativeRetryChain.context base noQuantum N count) N).quantumLayout
        Finset.univ Reference (stateTarget base noQuantum N count input)).trans
          (stateTarget_normalized base noQuantum N count input)))

/-- The independent complete state requirement holds for the same actual selected run. -/
theorem stateRequirement_holds (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference) :
    (stateRequirement base noQuantum N count).Holds input
      ((run base noQuantum specification count).finalState Reference input.state) :=
  fun value => StatePromise.mixed_fullSelection
    (context (NativeRetryChain.context base noQuantum N count) N).quantumLayout Reference
    (stateTarget base noQuantum N count input) (stateTarget_normalized base noQuantum N count input)
    _ (output_statePromise base noQuantum N count specification input value)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
