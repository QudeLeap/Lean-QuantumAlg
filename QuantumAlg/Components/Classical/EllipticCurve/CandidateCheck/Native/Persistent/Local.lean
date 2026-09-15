/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Execution.Local.Retained

/-!
# Local execution beside the existing persistent recovery cells

The original seven recovery cells remain resident while the same local
quantum sampling instructions run. Their actual accepted, selected, inverse,
candidate, reconstruction, target-acceptance and scalar roles use the original
context and keys. This extension emits no allocation; the caller retains the
cells once before entering its finite sampling and candidate-check loop.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def besideCell (localCode : { code : Circuit ctx ctx // code.IsLocal })
    (shape : CShape) :
    { code : Circuit (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh)
        (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh) //
      code.IsLocal } :=
  ⟨Circuit.underRetained localCode.val localCode.property ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh,
    Circuit.underRetained_isLocal localCode.val localCode.property ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh⟩

private def besidePersistent (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    { extended : Circuit (persistentCtx ctx width scalarWidth)
        (persistentCtx ctx width scalarWidth) // extended.IsLocal } :=
  let accepted := besideCell ⟨code, supported⟩ .bit
  let selected := besideCell accepted (.unsignedWord scalarWidth)
  let inverse := besideCell selected .bit
  let candidate := besideCell inverse (.unsignedWord scalarWidth)
  let reconstruction := besideCell candidate .bit
  let verified := besideCell reconstruction .bit
  besideCell verified (PointShape width)

/-- Run the same local instructions beside all seven existing recovery destinations. -/
def underPersistent (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    Circuit (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  (besidePersistent code supported width scalarWidth).val

/-- The extension keeps the complete persistent context throughout each actual instruction. -/
theorem underPersistent_isLocal (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    (underPersistent code supported width scalarWidth).IsLocal :=
  (besidePersistent code supported width scalarWidth).property

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
