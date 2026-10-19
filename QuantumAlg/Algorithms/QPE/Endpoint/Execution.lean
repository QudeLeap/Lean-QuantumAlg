/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Specification
public import QuantumAlg.Algorithms.QPE.Construction
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Measure.Distribution
public import Mathlib.Analysis.Normed.Group.AddCircle
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Distribution
import all QuantumAlg.Algorithms.QPE.Restoration
import all QuantumAlg.Algorithms.QPE.Resources
import all QuantumAlg.Algorithms.QPE.Space
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete native quantum phase estimation

The supplied borrowed eigenstate, internally prepared phase word, actual
controlled-power ladder, individual Z writes and stored bit packing belong
to one execution. Its own probabilities establish the original phase-window
bound, while complete Output and unconditional joint borrowed restoration
retain every live physical system and its reference correlations.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete public execution prepares, measures and returns its actual retained phase bits. -/
public def algorithm (n : Nat) (t : Nat) :
    Algorithm (model n) (pre t n) (post t n) (.bits t) where
  run := run n t

end

end QuantumAlg.QuantumPhaseEstimation
