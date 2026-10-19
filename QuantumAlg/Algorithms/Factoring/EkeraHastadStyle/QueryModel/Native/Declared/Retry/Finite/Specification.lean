/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.State.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability

/-!
# Public clock and retry calibration for declared EH factoring

The circuit clock charges one unit for gates, granted oracle queries and
classical queries, and zero for preparation, measurement and classical
operations. The shared real calibration reserves half the target failure for the
separate one-time key exception. Completed algorithm contracts supply their
actual state and resource requirements.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

noncomputable section

variable {N : Nat}

/-- The original gate/query clock also charges every actual reset correction. -/
@[expose] public def circuitDuration (N : Nat) : Resource.Event (model N) → Nat
  | .gate _ => 1
  | .oracle _ => 1
  | .classicalQuery _ => 1
  | .preparation _ => 0
  | .measurement _ => 0
  | .classicalOperation _ => 0

/-- The public gate/query clock charges each granted group-oracle call once. -/
public lemma circuitDuration_oracle (N : Nat) (coordinate) :
    circuitDuration N (.oracle coordinate) = 1 := rfl


variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
