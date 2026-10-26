/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput

/-! # The actual paid execution with the original caller Store recorded -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section
open Execution
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The actual run records precisely the original input Store
as its complete mathematical history. -/
lemma paidRun_execute_recorded (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference) :
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).execute environment Reference supplied.state =
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).code.execute environment Reference
        (suppliedState I supplied) := by
  unfold AlgorithmRun.execute suppliedState
  exact congrArg
    ((paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).code.execute environment Reference)
    (ExecutionState.executionState_mapClassical_congr_decision supplied.state
      (fun entry => (entry.1, (entry.2, entry.1)))
      (fun entry => (entry.1, (entry.2, entry.1))) (fun _ => rfl) _ _)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
