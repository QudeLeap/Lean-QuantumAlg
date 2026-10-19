/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual fixed-width classical scalar multiplication

The original infinity initialization precedes every declared scalar slot in
increasing, most-significant-bit-first order. Each slot performs complete
addition on the accumulator with itself, then reads its actual indexed bit
to select complete addition with the base point or identity. Leading zero
slots and the empty scalar width remain in the literal program.

Only structural references and the public curve specification determine the
program. The retained entry allocates its own result, keeping all original
input values separate from the accumulator without a caller separation or
initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The original stored-bit choice contains a real complete addition only for true. -/
def scalarBitArm (spec : CurveSpec width) (point : CInputRef ctx (PointShape width))
    (accumulator : CWriteRef ctx (PointShape width)) (value : CShape.Value .bit) :
    Circuit model ctx ctx :=
  if value.toBool then
    Add.Native.addInto spec (Add.Native.classifierRead accumulator) point accumulator
  else .id ctx

/-- Each original slot doubles first, then reads its actual indexed most-significant-first bit. -/
def scalarSlot (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) : Circuit model ctx ctx :=
  .seq (Add.Native.addInto spec (Add.Native.classifierRead accumulator)
    (Add.Native.classifierRead accumulator) accumulator)
    (.branch (.vectorGet bits index) (scalarBitArm spec point accumulator))

/-- Every declared scalar slot runs once in its original increasing finite-index order. -/
def scalarFold (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width)) :
    Circuit model ctx ctx :=
  Circuit.forRange scalarWidth (scalarSlot spec bits point accumulator)

/-- The actual infinity constructor precedes the complete original scalar fold. -/
def scalarInto (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width)) :
    Circuit model ctx ctx :=
  .seq (Add.Native.infinityInto accumulator) (scalarFold spec bits point accumulator)

/-- Allocate the original retained point result before the same literal scalar program. -/
def scalarRetained (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit model ctx (ctx.addRetained key (PointShape width) fresh) :=
  .seq (.retain ctx key (PointShape width) fresh)
    (scalarInto spec (bits.underRetained key (PointShape width) fresh)
      (point.underRetained key (PointShape width) fresh)
      (CWriteRef.retainedHead ctx key (PointShape width) fresh))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
