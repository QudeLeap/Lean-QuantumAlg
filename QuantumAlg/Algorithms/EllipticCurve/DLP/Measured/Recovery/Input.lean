/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Contract
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Support
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent original-input problem for the complete streaming execution

The local domain fixes only the original two public affine points. Every
normalized external reference extension is still admitted. Native budgets
depend only on the declared curve, subgroup order and finite retry count;
the specification receives no algorithm, execution path or resource account.

The original accepted scalar relation, exceptional-error calibration and
success threshold are retained. Borrowed restoration remains a mandatory
Solves obligation even though the original state-requirement list is empty.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Spec

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Both borrowed public point values are the complete original caller input. -/
def inputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  Recovery.PublicInput.frame E (orderWidth (ECDLP.Canonical.problem I))

/-- The final context retains the complete physical bank and native checked result. -/
def outputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  batchResultCtx (Recovery.PublicInput.context E (orderWidth (ECDLP.Canonical.problem I)))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth (ECDLP.Canonical.problem I))

end

end ExecutionContract.Spec
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
