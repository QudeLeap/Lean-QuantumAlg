/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.SourceLaw

/-!
# Actual EH sample against its selected mathematical law

The physical declared-query sample has the same conditional exponent PMF as
the original selected mathematical short-DLP sample, including arbitrary
caller-store, hidden-service-state and reference correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

/-- The source Born weight is the original selected short-DLP law. -/
theorem sourceWeight_eq_selected {N : Nat} (input : Input N)
    (parameter : (ParameterShape N).Value)
    (outcome : Fin (measurementBits N) → Bool) :
    sourceWeight N input parameter outcome =
      ((selectedOutcomePMF parameter outcome).toReal : ℂ) := by
  exact congrArg (fun distribution : PMF (Fin (measurementBits N) → Bool) =>
    ((distribution outcome).toReal : ℂ))
    (Native.source_outcomePMF_eq_selected input parameter)

/-- The actual run returns the selected law weighted by the original complete
caller and external reference state. -/
theorem outputDistribution_selected (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (outcome : Fin (measurementBits N) → Bool) :
    (run base noQuantum N input parameter).outputDistribution original (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun entry _ =>
            ((selectedOutcomePMF (entry.1.read parameter) outcome).toReal : ℂ))
          reference reference).re := by
  simpa only [sourceWeight_eq_selected] using
    outputDistribution base noQuantum N input parameter original outcome

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
