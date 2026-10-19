/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing.Solves
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# One actual final option pack after the finite complete-round suffix

The existing first-success bit and selected word are encoded once, after all
requested rounds, by the original paid classical instruction. Its independent
deterministic contract restores borrowed observations and accounts for the
new real option cell. The chronological circuit still pays this terminal work;
it is not another quantum cycle and introduces no reset or quantum bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original single retained optional-result cell and native option-pack instruction. -/
public def finalPack (I : ECDLPInstance E) :
    Circuit (Sampling.executionModel I) (context I) (post I) :=
  packBatchResult (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- Independent certain encoding of the actual incoming first-success result cells.

**Input.** Any existing persistent store, joint service state and external reference.
**Output.** The original accepted bit and selected word encoded as one optional result,
with every prior live entry and borrowed observation retained.
**Resource budget.** One actual width-indexed native option-pack operation and
one new retained optional word beside both complete existing storage pools.
**Success.** Exact encoding of the actual incoming latches with probability one.
**Source.** The library's closed `CShape.packOption` semantics and original checked
batch's actual terminal instruction; no additional quantum computation is claimed.
-/
public def finalPackProblem (I : ECDLPInstance E) :
    Problem (Sampling.executionModel I) (context I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  BatchPacking.problem (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
