/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Context
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage

/-!
# Complete output of the empty-input sample

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

/-- All systems and actual classical results of the common sampler remain live. -/
@[reducible] public def post (t n : Nat) : RuntimeCtx .quantum :=
  Framed.post pre pre_quantumWires t n

def resultRef (t n : Nat) : CWriteRef (post t n) (.bits t) :=
  Framed.resultRef pre pre_quantumWires t n

end

end QuantumAlg.OrderFinding.Sampling
