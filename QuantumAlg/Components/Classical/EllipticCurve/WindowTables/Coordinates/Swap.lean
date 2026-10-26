/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Work.Swap

/-!
# The same coordinate arrays with exchanged scalar names

All actual physical references and protected input obligations are the
original ones. The alternate frame only names the product/temporary cells
in the order used by the original secant suffix and destination writes.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Reuse the original two arrays and four words under the two exchanged scalar names. -/
def swapProductTemporary (frame : CoordinateFrame ctx width length) :
    CoordinateFrame ctx width length where
  x := frame.x
  y := frame.y
  separate := frame.separate
  work := frame.work.swapProductTemporary
  modulus := frame.modulus
  curveA := frame.curveA
  protectedCoefficient := by
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact frame.protectedCoefficient _ (by simp [Work.swapProductTemporary])

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
