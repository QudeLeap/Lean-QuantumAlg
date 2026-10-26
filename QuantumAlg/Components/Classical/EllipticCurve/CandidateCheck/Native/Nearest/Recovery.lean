/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native

/-!
# Paid nearest recovery through actual candidate verification and first-success selection

The existing native verifier and selector consume the actual nearest decoder's
three exposed cells.  All chronological stores, path records, caller reads,
Reference matrices and prior History labels remain part of the same execution.
The generic truncated-range decoder and its existing consumers are unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

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
  .seq (FiniteCyclicDLP.RawRecovery.Nearest.singleIntoCells modulus sample
      inverseSuccess candidate reconstruction)
    (verifyInto curve (.storage candidate.toCStorageRef) base target
      (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
      scalarResult accepted)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
