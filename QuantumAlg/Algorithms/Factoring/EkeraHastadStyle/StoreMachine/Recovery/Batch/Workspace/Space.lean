/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Space

/-!
# Exact classical capacity of all eight batch workspace packages

The persistent selector, six pair packages and independent quadratic package
coexist during recovery. Their bit counts are added once, independently of
the number of sequential pair invocations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace

/-- Independent bit count for the complete simultaneous batch allocation. -/
def allocationBits (N : Nat) : Nat :=
  2 * LatticeBatchRecoveryWorkspaceLayout.FactorWidth N + modulusBits N + 3 +
    LatticePairRecoveryWorkspace.allocationBits N + QuadraticScratchLayout.allocationBits N

private theorem batchSpaceArithmetic {kind : ProblemKind}
    (factor modulus pair quadratic : Nat) :
    ((([.unsignedWord factor, .bit, .unsignedWord factor, .bit, .bit,
      .unsignedWord modulus].map SpacePool.ofShape).sum + SpacePool.ofShape (.bits pair) +
        SpacePool.ofShape (.bits quadratic)) : SpacePool kind) =
      SpacePool.ofShape (.bits (2 * factor + modulus + 3 + pair + quadratic)) := by
  ext axis
  cases axis <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SpacePool.ofShape, Pi.add_apply, Pi.zero_apply, CShape.bitWidth] <;> omega

/-- Every actually allocated batch bit is accounted for, with no additional quantum system. -/
theorem batchAllocationSpace_eq_bits {kind : ProblemKind} (N : Nat) :
    (allocationSpace N : SpacePool kind) = SpacePool.ofShape (.bits (allocationBits N)) := by
  rw [allocationSpace, LatticePairRecoveryWorkspace.pairAllocationSpace_eq_bits,
    QuadraticScratchLayout.quadraticAllocationSpace_eq_bits]
  exact batchSpaceArithmetic (LatticeBatchRecoveryWorkspaceLayout.FactorWidth N) (modulusBits N)
    (LatticePairRecoveryWorkspace.allocationBits N) (QuadraticScratchLayout.allocationBits N)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace
