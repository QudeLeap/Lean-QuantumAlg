/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program

/-!
# Independent count bound for the complete allocated batch recovery

The actual eight lexical workspace packages preserve the native trace of the
complete recovery body. Every emitted operation, including initialization,
reusable pair clearing, the 120 pair invocations and output packing, satisfies
the same independent width polynomial after the caller result is preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The complete allocated caller program satisfies the independent fixed-batch event bound. -/
theorem fixedBatchRecovery_eventCount_le (input : Input N)
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).Path) :
    ((LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).eventTrace
      path).length ≤
      fixedBatchRecoveryCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (LatticePairCandidateRecovery.Width N) := by
  have bound : ∀ selected :
      (LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).Path,
      ((LatticeFixedBatchRecoveryMachine.into ctx input parameter terminals result).eventTrace
        selected).length ≤
        fixedBatchRecoveryCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (LatticePairCandidateRecovery.Width N) := by
    unfold LatticeFixedBatchRecoveryMachine.into
    apply LatticeBatchRecoveryWorkspace.withWorkspaces_property ctx N _
      (fun code => ∀ selected : code.Path, (code.eventTrace selected).length ≤
        fixedBatchRecoveryCardBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (LatticePairCandidateRecovery.Width N))
    · intro inner key shape fresh code available
      exact available
    · intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
      exact batchBody_eventCount_le input
        (LatticeFixedBatchRecoveryMachine.bodyRefs parameter terminals result top topTransport
          cells pairTransport)
  exact bound path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
