/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery
import all QuantumAlg.Components.Classical.FirstAccepted.Placement

/-!
# One original recovery, verification and first-success attempt

The actual raw recovery, scalar multiplication, point comparison and two
success conjunctions precede the original first-success selector. Its two
real decision bits are released within this attempt. All seven persistent
destinations remain in the same caller context for the next actual sample.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- All six original stages run in order on the same seven persistent destinations. -/
def attemptInto (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth)) :
    Circuit ctx ctx :=
  .seq (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted)
    (FirstAccepted.withSelection
      ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
