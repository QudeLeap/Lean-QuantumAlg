/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Grover.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Distribution
import all QuantumAlg.Algorithms.Grover.Restoration
import all QuantumAlg.Algorithms.Grover.Resources
import all QuantumAlg.Algorithms.Grover.Space
import all QuantumAlg.Algorithms.Grover.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Grover's complete native endpoint

The named algorithm contains the one actual prepare, Grover-unitary, Z-write
and packing execution. Its explicit complete output keeps every quantum
system and classical cell. The exact probability and native gate/query
counts are proved on this execution in addition to the independent Solves
contract [dW19, qcnotes.tex:2760-2852].
-/

namespace QuantumAlg.GroverSearch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete prepared search execution, with actual measured-result storage and full Output. -/
public def algorithm (n : Nat) (k : Nat) :
    Algorithm (model n) pre (post n k) (.bits n) where
  run := run n k

end

end QuantumAlg.GroverSearch
