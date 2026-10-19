/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.DeutschJozsa.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Algorithms.DeutschJozsa.Construction
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Algorithms.DeutschJozsa.Specification
import all QuantumAlg.Algorithms.DeutschJozsa.DistributionLaws
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# The complete native Deutsch-Jozsa endpoint

The sole executable circuit prepares the query and target, executes the
original oracle circuit, writes each query measurement to its own finite
classical cell, and packs the actual results. Complete Output retains every
live entry. The proof uses probabilities and paths from that same execution,
including preservation of its borrowed classical input and arbitrary
external-reference correlations.
-/

namespace QuantumAlg.DeutschJozsa

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual internally prepared circuit, with n real Z writes and complete live Output. -/
public def algorithm (n : Nat) :
    Algorithm (model n) pre (post n) (.bits n) where
  run := run n

end

end QuantumAlg.DeutschJozsa
