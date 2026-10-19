/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Sound
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability
import all QuantumAlg.Core.Execution.Reference.Probability.Kernel

/-!
# The original source transition of actual complete feedback

The transition kernel depends on the incoming actual latch. Each source draw
uses the original sample and Born law. Full recovery and feedback retain the
first present result, and physical reset is part of the observed execution.
The complete reference equation determines the same actual trace-derived PMF.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

local instance {N : Nat} : Fintype (SourceOutcome N) :=
  Fintype.ofEquiv (Fin (2 ^ residueSamplingBits N) × TerminalZMeasure.Outcome (phaseBits N))
    (SourceWeights.outcomeEquiv N)

/-- The original source updates an actual old latch by chronological first-present selection. -/
def completionKernel {N : Nat} (input : Input N)
    (old : CShape.Value (.option (.unsignedWord (modulusBits N)))) :
    PMF (CShape.Value (.option (.unsignedWord (modulusBits N)))) :=
  (sourceOutcomePMF input).map
    (fun outcome => NativeFactorScan.firstPresent old (NativeFactorScan.sourceResult input outcome))

private lemma completionKernel_indicator {N : Nat} (input : Input N)
    (old value : CShape.Value (.option (.unsignedWord (modulusBits N)))) :
    SourceWeights.one input (fun outcome =>
      if NativeFactorScan.firstPresent old (NativeFactorScan.sourceResult input outcome) = value
      then 1 else 0) = ((completionKernel input old value).toReal : ℂ) := by
  rw [SourceWeights.one_eq]
  exact PMF.sum_toReal_map_indicator (sourceOutcomePMF input)
    (fun outcome => NativeFactorScan.firstPresent old (NativeFactorScan.sourceResult input outcome))
    value

/-- Actual complete-round readout has the source kernel conditioned on the real incoming latch. -/
lemma Completion.latch_toPMF (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized) :
    (((Completion.code ctx N input sameWires cells result).execute
      (environment input) Reference state).toPMF
      (((Completion.code ctx N input sameWires cells result).execute_mass
        (environment input) Reference state).trans
        normalized)).map
      (fun entry => NativeFactorScan.latchValue (Completion.cells ctx N cells) entry.1) =
    (state.toPMF normalized).bind
      (fun entry => completionKernel input (NativeFactorScan.latchValue cells entry.1)) := by
  apply ExecutionState.toPMF_map_eq_bind_of_referenceFiberSum state
    ((Completion.code ctx N input sameWires cells result).execute
      (environment input) Reference state) normalized
    (((Completion.code ctx N input sameWires cells result).execute_mass
      (environment input) Reference state).trans
      normalized)
  intro value left right
  have actual := completion_latch_reference ctx N input sameWires cells result separated
    state seeded normalized (fun selected => if selected = value then 1 else 0) left right
  refine actual.trans ?_
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact completionKernel_indicator input (NativeFactorScan.latchValue cells entry.1) value

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
