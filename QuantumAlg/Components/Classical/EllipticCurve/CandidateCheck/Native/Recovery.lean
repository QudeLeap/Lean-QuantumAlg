/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native

/-!
# Actual original recovery followed by candidate verification

The original raw recovery exposes its three actual observations before the
original scalar multiplication, point comparison and two conjunctions execute.
Every stage uses the same caller context and persistent destinations. A later
attempt reuses these destinations without retaining additional cells. The
first-success selector follows this actual five-stage recovery and check.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The original raw recovery and all four verification stages share the actual caller cells. -/
def recoveryInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  .seq (FiniteCyclicDLP.RawRecovery.Native.singleIntoCells modulus sample
      inverseSuccess candidate reconstruction)
    (verifyInto curve (.storage candidate.toCStorageRef) base target
      (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
      scalarResult accepted)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
