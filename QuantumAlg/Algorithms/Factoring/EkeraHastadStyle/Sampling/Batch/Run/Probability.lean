/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Output.Probability

/-!
# The actual complete run has the original batch output distribution

Entering an AlgorithmRun records the original store only as mathematical
history. The real code and full Output then yield the same source PMF proved
for arbitrary histories. No extra live register is allocated for that record,
and the input's complete quantum-reference correlations remain admissible.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The real run enters the same code while recording the original caller store as history. -/
theorem nativeBatch_run_enter (Reference : Register)
    (state : ExecutionState (Store base) (Register.prod base.register Reference)) :
    (run base noQuantum N).execute Reference state =
      (code base noQuantum N).execute Reference
        (state.mapClassical (fun store => (store, store))) := by
  unfold AlgorithmRun.execute
  apply congrArg (fun initial : State base Reference (Store base) =>
    (code base noQuantum N).execute Reference initial)
  congr 1

/-- The complete run's actual Output probabilities have the original same-source batch law. -/
theorem nativeBatch_run_outputDistribution (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum N).outputDistribution input = sourceDistribution specification := by
  let entered : State base Reference (Store base) :=
    input.state.mapClassical (fun store => (store, store))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun store => (store, store))
  have actual : (run base noQuantum N).executionDistribution input =
      ((code base noQuantum N).execute Reference entered).toPMF
        (((code base noQuantum N).execute_mass Reference entered).trans normalized) := by
    apply PMF.ext
    intro record
    exact congrArg
      (fun final : ExecutionState (run base noQuantum N).Record
          (Register.prod (context base noQuantum N).register Reference) =>
        ENNReal.ofReal (final.block record).mass)
      (nativeBatch_run_enter base noQuantum N Reference input.state)
  have observed := congrArg
    (fun distribution : PMF (run base noQuantum N).Record =>
      distribution.map (fun record => (run base noQuantum N).output.eval record.1)) actual
  exact observed.trans
    (nativeBatch_output_toPMF base noQuantum specification entered normalized)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
