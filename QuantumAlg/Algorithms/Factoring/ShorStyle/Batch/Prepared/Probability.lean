/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.Interpret

/-!
# Original independent-source probabilities from one actual prepared Shor bank

The actual preparation supplies the seed without any supplied seed or product
state premise. The complete batch uses its actual repeated sampler and reset
paths. Its reference observations therefore have the original source-vector
law, and the same executed density blocks give exactly that output PMF.
Arbitrary initial classical-reference correlations are retained throughout.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
  {N : Nat} (source : Input N) (count : Nat)

/-- Complete result weights come from the original source law and the unchanged incoming Ref. -/
theorem code_referenceFiberSum_result {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (weight : (CShape.fixedVector count (NativeIteration.resultShape N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code ctx noQuantum N count).execute Reference state)
        (fun entry _ => weight (entry.1.read
          (NativeBatch.readout (NativeBank.context ctx noQuantum N) N count)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => SourceWeights.batch source count
          (fun outcomes => weight
            (.fixedVector (fun index => NativeBatch.sourceValue source (outcomes index)))))
        leftRef rightRef := by
  let prepared := NativeBank.prepare ctx noQuantum N
  let rounds := NativeBatch.code (NativeBank.context ctx noQuantum N) N
    (NativeBank.quantumWires ctx noQuantum N) count
  let empty : CInputRef (NativeBank.context ctx noQuantum N) (.fixedVector 0 .bit) :=
    .fixedVector Fin.elim0
  let coefficient := SourceWeights.batch source count
    (fun outcomes => weight
      (.fixedVector (fun index => NativeBatch.sourceValue source (outcomes index))))
  have sequence := Circuit.referenceFiberSum_execute_seq prepared rounds state
    (fun store => weight (store.read
      (NativeBatch.readout (NativeBank.context ctx noQuantum N) N count))) leftRef rightRef
  have actual := NativeBatch.code_referenceFiberSum_input source count
    (NativeBank.quantumWires ctx noQuantum N) empty (prepared.execute Reference state)
    (NativeBank.prepare_seeded ctx noQuantum N state)
    (fun _ values => weight (.fixedVector values)) leftRef rightRef
  have initialized := Circuit.referenceFiberSum_execute_prepare ctx.canonicalFreshKey
    (NativeQuantum.runtimeLayout N) ctx.canonicalFreshKey_fresh
    (NativeBank.allocationDisjoint ctx noQuantum N) (NativeQuantum.seedPreparation N) state
    (fun _ => coefficient) leftRef rightRef
  exact sequence.trans (actual.trans initialized)

/-- The actual result PMF is the original source's independent finite vector, in stored encoding. -/
theorem code_outputPMF {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (normalized : state.IsNormalized) :
    (((code ctx noQuantum N count).execute Reference state).toPMF
      (((code ctx noQuantum N count).execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read
          (NativeBatch.readout (NativeBank.context ctx noQuantum N) N count)) =
      (PMF.independentReplicateVector (sourceOutcomePMF source) count).map
        (fun outcomes => CShape.Value.fixedVector
          (fun index => NativeBatch.sourceValue source (outcomes.get index))) := by
  refine ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((code ctx noQuantum N count).execute Reference state) normalized
    (((code ctx noQuantum N count).execute_mass Reference state).trans normalized)
    (fun entry => entry.1.read
      (NativeBatch.readout (NativeBank.context ctx noQuantum N) N count)) _ ?_
  intro selected leftRef rightRef
  have actual := code_referenceFiberSum_result ctx noQuantum source count state
    (fun value => if value = selected then 1 else 0) leftRef rightRef
  have sourceProbability := SourceWeights.batch_indicator source count
    (fun outcomes => CShape.Value.fixedVector
      (fun index => NativeBatch.sourceValue source (outcomes index))) selected
  exact actual.trans (congrArg (fun coefficient : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => coefficient) leftRef rightRef)
      sourceProbability)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch
