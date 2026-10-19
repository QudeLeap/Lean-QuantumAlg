/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Distribution
import all QuantumAlg.Core.Execution.State.Readout

/-!
# Full owned-bank and reference output blocks of the actual initialized Shor machine

The packed result is observed in the same complete execution that restores the
physical bank to zero. Every result block, including zero-mass results, has
the original external-reference state and the original source probability.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every actual output block preserves the full original reference with the zero owned bank. -/
lemma code_output_entry (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History))
    (normalized : state.IsNormalized)
    (value : CShape.Value (.option (.unsignedWord (modulusBits N))))
    (left right : (context base noQuantum N count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code base noQuantum N input count).execute (environment input) Reference state).mapClassical
      (fun entry => (run base noQuantum N input count).output.eval entry.1)).block value).matrix
        (left, leftRef) (right, rightRef) =
      if left = (context base noQuantum N count).quantumLayout.zeroLabel ∧
          right = (context base noQuantum N count).quantumLayout.zeroLabel then
        ((sourceDistribution input count value).toReal : ℂ) *
          state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  have observed := BasisSeeded.readout_entry
    (context base noQuantum N count).quantumLayout.zeroLabel
    ((code base noQuantum N input count).execute (environment input) Reference state)
    (code_seeded (environment := environment input) base noQuantum N input count state)
    (fun store => store.read (.storage (result base noQuantum N count).toCStorageRef))
    value left right leftRef rightRef
  have actual := code_output_point_reference base noQuantum N input count state normalized
    value leftRef rightRef
  have scalar := actual.trans (ExecutionState.referenceFiberSum_constant_eq state
    ((sourceDistribution input count value).toReal : ℂ) leftRef rightRef)
  exact observed.trans (congrArg (fun coefficient : ℂ =>
    if left = (context base noQuantum N count).quantumLayout.zeroLabel ∧
        right = (context base noQuantum N count).quantumLayout.zeroLabel then coefficient
    else 0) scalar)

/-- The actual complete run promises the zero owned bank on every original-reference result. -/
lemma output_state (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput (executionModel N).classicalOracles base Reference)
    (value : CShape.Value (.option (.unsignedWord (modulusBits N)))) :
    (StatePromise.mixed
      (BasisReference.target (R := (context base noQuantum N count).register)
        (context base noQuantum N count).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal)
      (BasisReference.target_normalized (R := (context base noQuantum N count).register)
        (context base noQuantum N count).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass original.caller.state).trans
          original.caller.normalized))).Holds
      ((((run base noQuantum N input count).finalState (environment input) Reference
        original.state).mapClassical
        (run base noQuantum N input count).output.eval).block value) :=
  AlgorithmRun.basisReference_readout_of_executionEntries (environment := environment input)
    (run base noQuantum N input count)
    (context base noQuantum N count).quantumLayout.zeroLabel (sourceDistribution input count)
    (code_output_entry base noQuantum N input count) original value

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
