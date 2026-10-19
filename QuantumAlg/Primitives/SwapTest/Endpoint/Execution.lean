/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.SwapTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.SwapTest.Specification
import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Probability
import all QuantumAlg.Primitives.SwapTest.Resources
import all QuantumAlg.Primitives.SwapTest.Restoration
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete elementary SWAP test with its exact scientific probability

The same complete measured execution supplies the source probability,
independent native resource limits and external reference restoration
[BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Only the complete native run is stored in the public algorithm. -/
public def algorithm (width : Nat) : Algorithm model (pre width) (post width) (.finite 2) :=
  ⟨run width⟩

end

end QuantumAlg.SwapTest
