/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Complete
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Actual declared EH output distribution

The registered run returns the packed exponent bits from its real result
cell. Its PMF is the trace of the same complete execution whose conditional
Born reference law was proved for the original caller input.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual packed result PMF traces the conditional source Born law
against the original correlated caller, service and reference state. -/
theorem outputDistribution (parameter : CInputRef base (ParameterShape N))
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (outcome : Fin (measurementBits N) → Bool) :
    (run base noQuantum N input parameter).outputDistribution original (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun entry _ => sourceWeight N input (entry.1.read parameter) outcome)
          reference reference).re := by
  let actual := run base noQuantum N input parameter
  let read := fun record : actual.Record => actual.result record
  have mapped := congrArg
    (fun probability : PMF (CShape.Value (.bits (measurementBits N))) =>
      probability (.bits outcome))
    (ExecutionState.toPMF_mapClassical
      (actual.execute Reference original.state)
      (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply,
    ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro reference _
  exact (code_outcome_reference base noQuantum N input parameter
    (original.state.mapClassical
      (fun entry => (entry.1, (entry.2, entry.1))))
    outcome reference reference).trans
    (ExecutionState.referenceFiberSum_mapClassical original.state
      (fun entry => (entry.1, (entry.2, entry.1))) _ reference reference)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
