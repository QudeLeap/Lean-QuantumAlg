/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local

/-!
# Actual path beside the seven existing recovery cells

The seven existing cell extensions add no outcome choice. Their canonical
path equivalences are composed in the original shape and allocation order.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def besidePath {base outer : RuntimeCtx kind} {code : Circuit base base}
    (localCode : { code : Circuit outer outer // code.IsLocal }) (shape : CShape)
    (path : code.Path ≃ localCode.val.Path) : code.Path ≃ (besideCell localCode shape).val.Path :=
  path.trans (Circuit.underRetainedPathEquiv localCode.val localCode.property
    outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh)

/-- The original actual path acquires no choice from the seven existing cells. -/
def underPersistentPathEquiv (code : Circuit ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    code.Path ≃ (underPersistent code supported width scalarWidth).Path :=
  let original := (⟨code, supported⟩ : { code : Circuit ctx ctx // code.IsLocal })
  let accepted := besideCell original .bit
  let selected := besideCell accepted (.unsignedWord scalarWidth)
  let inverse := besideCell selected .bit
  let candidate := besideCell inverse (.unsignedWord scalarWidth)
  let reconstruction := besideCell candidate .bit
  let verified := besideCell reconstruction .bit
  besidePath verified (PointShape width)
    (besidePath reconstruction .bit (besidePath candidate .bit
      (besidePath inverse (.unsignedWord scalarWidth)
        (besidePath selected .bit (besidePath accepted (.unsignedWord scalarWidth)
          (besidePath original .bit (Equiv.refl _)))))))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
