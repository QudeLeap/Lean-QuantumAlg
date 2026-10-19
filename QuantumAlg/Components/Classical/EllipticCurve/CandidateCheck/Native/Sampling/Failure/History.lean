/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure

/-!
# Failure weight does not depend on path history

The retained acceptance bit belongs to the store. Reassociating or recording
circuit paths cannot change its subnormalized failure mass.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

variable {model : ExecutionModel} {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

lemma persistentFailureWeight_mapHistory
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × H))
    (update : model.HiddenState × H → model.HiddenState × K) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      (state.mapHistory update) =
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      state := by
  unfold persistentFailureWeight
  rw [State.effectWeight_mapHistory]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
