/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Solves
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# The original positive finite ECDLP run has actual complete cycles

The first cycle contains all initial allocation and one full checked round.
Every further requested round is separately complete and physically admitted.
One classical result pack ends the original run. Structural reassociation only
changes sequence parentheses, retaining its complete states, paths, events,
chronological depth and both storage peaks. The zero-round endpoint is a
separate initialization-and-packing computation, not a restartable prefix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private def positiveAssociation (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat) :
    Circuit.Reassociation (code I expansion nontrivial (further + 1))
      ((firstRound I expansion nontrivial).seq
        ((reusedRounds I expansion nontrivial further).seq (finalPack I))) := by
  let initial := Sampling.Reuse.initialCode I
  let retain := retainPersistent (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
  let body := round I expansion nontrivial
  let rest := reusedRounds I expansion nontrivial further
  let pack := finalPack I
  exact (Circuit.Reassociation.seq (.refl initial) (.seqAssoc retain (body.seq rest) pack)).trans
    ((Circuit.Reassociation.seq (.refl initial)
      (.seq (.refl retain) (.seqAssoc body rest pack))).trans
      ((Circuit.Reassociation.seqAssoc initial retain (body.seq (rest.seq pack))).symm.trans
        (Circuit.Reassociation.seqAssoc (initial.seq retain) body (rest.seq pack)).symm))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
