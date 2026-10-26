/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Specification
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification

/-!
# The retained preparation invariant supplies each actual chronological driver

The four constants remain a single shared invariant. One selected row is
derived from the original paired families at the point of use.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve.WindowTables

/-- The same prepared Store supplies all six reads of the current real point driver. -/
lemma driverInputValues_of_paired_rows {ctx : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance) (frame : Outer.Frame ctx 256)
    (store : Store ctx)
    (constants : Outer.Preparation.Signed.Constants frame (actualCurveSpec I) store)
    (rows : Outer.Preparation.Signed.pairedRows (actualCurveSpec I) frame
      (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey store)
    (position : Fin 34) :
    Driver.driverInputValues frame (actualCurveSpec I) (chronologicalBasePoint I position)
      (Sampling.chronologicalIndex position).row store := by
  have paired := (Outer.Preparation.Signed.pairedRows_iff (actualCurveSpec I) frame
    (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey store).mp rows
  have selected := chronologicalBasePoint_coordinateValue_of_paired_rows
    I frame store paired.1 paired.2 position
  exact ⟨constants.modulus, constants.zero, constants.one, constants.curveA, selected⟩

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
