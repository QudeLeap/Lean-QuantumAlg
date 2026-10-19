/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.BernsteinVazirani.Endpoint
import all QuantumAlg.Algorithms.BernsteinVazirani.Endpoint
import all QuantumAlg.Algorithms.BernsteinVazirani.Endpoint.Execution

public import QuantumAlg.Algorithms.BernsteinVazirani.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.BernsteinVazirani.Construction
import all QuantumAlg.Algorithms.BernsteinVazirani.Specification
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native Bernstein-Vazirani recovery

The hidden string supplies only the inner-product oracle. The common
Walsh-Hadamard execution prepares its own quantum input and computes the
answer from actual Z writes and finite-bit packing. Its complete Output
retains every live entry. The exact mathematical recovery theorem is
connected to the same execution's final block probabilities, and its paths
satisfy the independent native budgets for every width, including zero.
-/

namespace QuantumAlg.BernsteinVazirani

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every local input state is admitted; normalization belongs to the execution Input. -/
public lemma problem_valid {n : Nat} (hidden : Fin (2 ^ n))
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n).valid (environment (oracle hidden)) hidden state := rfl

/-- The public output contract requires precisely the big-endian hidden-string encoding. -/
public lemma problem_returns_hidden_bits_iff {n : Nat} (hidden : Fin (2 ^ n))
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem n).accepts (environment (oracle hidden)) hidden initial (.bits outcome) ↔
      outcome = (fun index => hidden.val.testBit (n - 1 - index.val)) := Iff.rfl

end

end QuantumAlg.BernsteinVazirani
