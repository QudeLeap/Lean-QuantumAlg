/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Distribution
import all QuantumAlg.Primitives.HadamardTest.Restoration
import all QuantumAlg.Primitives.HadamardTest.Resources
import all QuantumAlg.Primitives.HadamardTest.Space
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete native Hadamard test with its exact scientific probability

The algorithm prepares one control, executes the actual controlled source
query, measures into a finite classical register, and reads that register.
Its same execution satisfies the independent event, space and depth limits,
complete borrowed-reference restoration, and the original exact probability
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The algorithm contains only the same complete native run. -/
public def algorithm (width : Nat) :
    Algorithm (model width) (pre width) (post width) (.finite 2) := ⟨run width⟩

end

end QuantumAlg.HadamardTest
