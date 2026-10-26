/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Recovery
import all QuantumAlg.Components.Classical.FirstAccepted.Placement

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

/-- All six original stages run in order on the same seven persistent destinations. -/
def attemptInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth)) :
    Circuit model ctx ctx :=
  .seq (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted)
    (FirstAccepted.withSelection
      ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
