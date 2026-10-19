/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.FixedOffset
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# One actual streaming algorithm solves the original measured ECDLP problem

The same complete allocation, reset, converted sampler, native checked retry
and final packing execution supplies every Solves field. Success retains the
original affine-addend and full exceptional-error calibration. No caller
cleanliness, prepared bank, point-interpretation or independent resource
certificate is introduced. The actual borrowed point/reference observation
is restored separately from the original empty state-requirement list.


-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Solves

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma run_restores_of_noBorrowedQuantum {model : ExecutionModel}
    {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (actual : AlgorithmRun model pre post shape) (noBorrowed : pre.borrowedQuantumWires = [])
    {Reference : Register} (supplied : OracleInput model.classicalOracles pre Reference) :
    actual.RestoresBorrowed environment supplied := by
  let recorded := supplied.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have restored := actual.code.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    noBorrowed Reference
    recorded
  change observeBorrowedAfter actual.code Reference
      (actual.code.execute environment Reference recorded) = observeBorrowed Reference
        supplied.state
  have observed := observeBorrowed_mapClassical supplied.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  have recordedObservation : observeBorrowed Reference recorded =
      observeBorrowed Reference supplied.state := by
    convert observed using 1
    apply congrArg (fun state : State pre Reference (model.HiddenState × Store pre) =>
      observeBorrowed Reference state)
    exact ExecutionState.executionState_mapClassical_congr supplied.state rfl
  exact restored.trans recordedObservation

end

end ExecutionContract.Solves
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
