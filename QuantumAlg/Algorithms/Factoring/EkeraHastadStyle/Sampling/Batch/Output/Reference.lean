/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Distribution.Weights

/-!
# Actual complete batch Output jointly with every reference coordinate

The structural Output reads the real retained source, complete parameter and
sixteen chronological measurement results. Every finite weight of that output
is its original source-distribution weight times the same incoming reference
entry. This retains off-diagonal reference coherence and applies to arbitrary
incoming mass; normalization is needed only by the subsequent PMF statement.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution
open ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The actual complete Output has the source PMF's finite weight in each full reference entry. -/
lemma nativeBatch_output_weighted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (resultShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute environment Reference state)
        (fun entry _ => weight ((run base noQuantum N).output.eval entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : (resultShape N).Value,
          ((sourceDistribution input output).toReal : ℂ) * weight output) leftRef rightRef :=
  (nativeBatch_source_weighted_reference base noQuantum N input state
    (fun parameter sample outcomes => weight
      (.product sample (.product parameter (.fixedVector outcomes)))) leftRef rightRef).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) leftRef rightRef)
      (nativeBatch_sourceDistribution_weighted input weight).symm)

/-- Each real output fiber has the exact original source point mass in every reference entry. -/
lemma nativeBatch_output_indicator_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (selected : (resultShape N).Value)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute environment Reference state)
        (fun entry _ => if (run base noQuantum N).output.eval entry.1 = selected then 1 else 0)
        leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ((sourceDistribution input selected).toReal : ℂ)) leftRef rightRef :=
  (nativeBatch_output_weighted_reference base noQuantum input state
    (fun output => if output = selected then 1 else 0) leftRef rightRef).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) leftRef rightRef)
      (PMF.sum_toReal_indicator (sourceDistribution input) selected))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
