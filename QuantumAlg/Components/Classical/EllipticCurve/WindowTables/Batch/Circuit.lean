/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import all QuantumAlg.Components.Classical.Modular.NativePower.Placement
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual in-place batch inversion

The forward pass stores the preceding product in D and multiplies the actual
C entry into one scalar. One actual XGCD coefficient computation inverts the
complete product. The reverse pass uses two actual modular multiplications
and one paid C-row overwrite. Address zero is never visited by either pass.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

/-- Save the old running product before consuming this row's original denominator. -/
def forwardStep (index : Fin length) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
      (rowWriteOp frame.prefixes index (wordRead frame.work.product)))
    (scopedMultiply (wordRead frame.work.product) (rowRead frame.denominators index)
      frame.modulus frame.work.product)

/-- Recover the row inverse before advancing the accumulator with the still-original C entry. -/
def reverseStep (index : Fin length) : Circuit model ctx ctx :=
  .seq (scopedMultiply (wordRead frame.work.inverse) (rowRead frame.prefixes index)
      frame.modulus frame.work.temporary)
    (.seq (scopedMultiply (wordRead frame.work.inverse) (rowRead frame.denominators index)
        frame.modulus frame.work.inverse)
      (BitWord.instruction (execution := model)
        (rowWriteOp frame.denominators index (wordRead frame.work.temporary))))

/-- Visit the nonzero rows in increasing order, retaining row zero's original data. -/
def forwardPass (count : Nat) (fits : count < length) : Circuit model ctx ctx :=
  Circuit.forRange count fun index => frame.forwardStep ⟨index.val + 1, by omega⟩

/-- Visit exactly the same rows in reverse order before any original denominator is lost. -/
def reversePass (count : Nat) (fits : count < length) : Circuit model ctx ctx :=
  Circuit.forRange count fun index => frame.reverseStep ⟨count - index.val, by omega⟩

/-- One real coefficient computation is shared by all rows; an empty batch is identity. -/
def circuit (spec : ModulusSpec width) (count : Nat) (fits : count < length) :
    Circuit model ctx ctx :=
  if count = 0 then .id ctx else
    .seq (BitWord.instruction (execution := model)
        (.wordResize width width ctx frame.one frame.work.product))
      (.seq (frame.forwardPass count fits)
        (.seq (Field.Native.coefficientIntoWord spec (wordRead frame.work.product)
            frame.work.inverse)
          (frame.reversePass count fits)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
