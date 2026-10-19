/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Output.Reference
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# The actual complete native batch Output has the original source PMF

The output distribution below is read from the normalized blocks of the one
real sampler, bank preparation and sixteen-round execution. Its equality to
the original source PMF is obtained by tracing the already proved complete
reference fibers, not by assigning a separate distribution to the run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual normalized output probabilities equal the original same-source sixteen-round law. -/
lemma nativeBatch_output_toPMF (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat} (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (normalized : state.IsNormalized) :
    ((((code base noQuantum N).execute environment Reference state).toPMF
      (((code base noQuantum N).execute_mass environment Reference state).trans normalized)).map
        (fun record => (run base noQuantum N).output.eval record.1)) =
      sourceDistribution input :=
  ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((code base noQuantum N).execute environment Reference state) normalized
    (((code base noQuantum N).execute_mass environment Reference state).trans normalized)
    (fun record => (run base noQuantum N).output.eval record.1) (sourceDistribution input)
    (nativeBatch_output_indicator_reference base noQuantum input state)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
