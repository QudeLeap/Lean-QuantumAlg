/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Density
public import QuantumAlg.Core.Execution.State.Pure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Density

/-!
# Fixed physical zero on every complete reused-round record

The actual terminal reset leaves the whole original bank in zero within
every complete store, hidden-service and path block. The promise keeps each
block's actual mass, including zero, and its arbitrary quantum reference.
It supplies the state part of physical restart; protocol and next-input
admission remain separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every actual full-round record has the same fixed physical zero at its own mass. -/
public theorem ecdlpReuse_code_block_pure (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History))
    (record : Store (context I) ×
      ((executionModel I A).HiddenState × (History × (code I A expansion).Path))) :
    (StatePromise.pure (NormalizedVector.ket (R := (context I).register)
      (context I).quantumLayout.zeroLabel)).Holds
        (((code I A expansion).execute Reference state).block record).marginalLeft :=
  ExecutionState.block_pureKet_of_localMarginal ((code I A expansion).execute Reference state)
    (context I).quantumLayout.zeroLabel (ecdlpReuse_code_pure I A expansion state) record

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
