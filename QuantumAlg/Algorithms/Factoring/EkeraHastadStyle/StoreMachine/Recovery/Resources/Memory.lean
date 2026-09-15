/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program

/-!
# Explicit classical-memory bound of the complete actual batch recovery

The independent width formula counts all eight simultaneous workspace
packages and native modular-power scratch. The same actual path supplies
both resident and auxiliary bounds relative to the complete caller context.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

open ClassicalRoutines

/-- Closed classical-bit budget for all additional live storage in one complete recovery. -/
def fixedBatchRecoveryAdditionalBits (N : Nat) : Nat :=
  104 * LatticeWideLllMachine.Width N + 14 * modulusBits N + 4 * measurementBits N +
    2 * BatchMachine.JWidth N + 2 * BatchMachine.KWidth N +
    5 * QuadraticScratchLayout.DiscriminantWidth N +
    9 * QuadraticScratchLayout.CandidateWidth N + QuadraticScratchLayout.CenterWidth N +
    8 * QuadraticScratchLayout.WorkWidth N + 48

private theorem recoverySpaceArithmetic {kind : ProblemKind}
    (width modulus measured jWidth kWidth discriminant candidate center work : Nat) :
    ((SpacePool.ofShape (.bits (2 * candidate + modulus + 3 +
      (104 * width + 5 * modulus + 4 * measured + 2 * jWidth + 2 * kWidth + 33) +
      (5 * discriminant + 7 * candidate + center + 8 * work + 10))) +
      SpacePool.ofShape (.bits (8 * modulus + 2))) : SpacePool kind) =
      SpacePool.ofShape (.bits (104 * width + 14 * modulus + 4 * measured + 2 * jWidth +
        2 * kWidth + 5 * discriminant + 9 * candidate + center + 8 * work + 48)) := by
  ext axis
  cases axis <;> simp only [SpacePool.ofShape, Pi.add_apply, CShape.bitWidth]
  omega

/-- The independent additional-space pool has exactly the displayed classical-bit formula. -/
theorem fixedBatchRecovery_additionalSpace_eq_bits {kind : ProblemKind} (N : Nat) :
    (LatticeFixedBatchRecoveryMachine.additionalSpace N : SpacePool kind) =
      SpacePool.ofShape (.bits (fixedBatchRecoveryAdditionalBits N)) := by
  rw [LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits]
  exact recoverySpaceArithmetic (LatticeWideLllMachine.Width N) (modulusBits N) (measurementBits N)
    (BatchMachine.JWidth N) (BatchMachine.KWidth N) (QuadraticScratchLayout.DiscriminantWidth N)
    (QuadraticScratchLayout.CandidateWidth N) (QuadraticScratchLayout.CenterWidth N)
    (QuadraticScratchLayout.WorkWidth N)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Every actual resident peak includes the caller plus the explicit extra classical capacity. -/
theorem fixedBatchRecovery_resident_le_bits (input : Input N)
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).Path) :
    (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).peakResidentSpace
      path ≤
      SpacePool.ofShape (.bits (fixedBatchRecoveryAdditionalBits N)) + ctx.residentSpace := by
  rw [← fixedBatchRecovery_additionalSpace_eq_bits]
  exact LatticeFixedBatchRecoveryMachine.into_resident_le input parameter terminals result path

/-- Every actual auxiliary peak includes the same complete additional classical capacity. -/
theorem fixedBatchRecovery_auxiliary_le_bits (input : Input N)
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).Path) :
    (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).peakAuxiliarySpace
      path ≤
      SpacePool.ofShape (.bits (fixedBatchRecoveryAdditionalBits N)) + ctx.auxiliarySpace := by
  rw [← fixedBatchRecovery_additionalSpace_eq_bits]
  exact LatticeFixedBatchRecoveryMachine.into_auxiliary_le input parameter terminals result path

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
