/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Frame
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient
import all QuantumAlg.Components.Classical.Modular.NativePower.Placement
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual row programs for five-array table construction

Each arithmetic step is an existing closed native instruction sequence.
Four scalar words are overwritten in a fixed order. Source coordinates
remain in X/Y while C/D successively hold denominators, inverses and prefix
products. The final row conversion writes -x, -y, 3x, the tangent slope at
-Q and x+1; its field-domain interpretation is a separate correctness proof.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "i" => wordRead frame.work.inverse
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope
local notation "modulus" => wordRead frame.modulus

/-- Actual initial base coordinates are copied into their first nonzero table row. -/
def seedRow (index : Fin length) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x index frame.baseX))
    (BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y index frame.baseY))

/-- Actual shared-modulus doubling, with its final two writes made directly into the seed row. -/
def doubleRow (spec : ModulusSpec width) (source destination : Fin length) :
    Circuit model ctx ctx :=
  let x := rowRead frame.arrays.x source
  let y := rowRead frame.arrays.y source
  Circuit.forRange 15 ![
    Field.Native.Shared.addIntoWord y y modulus frame.work.product,
    Field.Native.coefficientIntoWord spec p frame.work.inverse,
    scopedMultiply x x modulus frame.work.temporary,
    Field.Native.Shared.addIntoWord t t modulus frame.work.product,
    Field.Native.Shared.addIntoWord p t modulus frame.work.product,
    Field.Native.Shared.addIntoWord p frame.curveA modulus frame.work.product,
    scopedMultiply p i modulus frame.work.slope,
    Field.Native.Shared.addIntoWord x x modulus frame.work.product,
    scopedMultiply s s modulus frame.work.temporary,
    Field.Native.Shared.subIntoWord t p frame.modulus frame.work.product,
    Field.Native.Shared.subIntoWord x p frame.modulus frame.work.temporary,
    scopedMultiply s t modulus frame.work.temporary,
    Field.Native.Shared.subIntoWord t y frame.modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x destination p),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y destination t)]

/-- One paid denominator computation prepares the current binary layer's nonseed row. -/
def denominatorRow (seed row : Fin length) : Circuit model ctx ctx :=
  .seq (Field.Native.Shared.subIntoWord
      (rowRead frame.arrays.x seed) (rowRead frame.arrays.x row)
      frame.modulus frame.work.temporary)
    (BitWord.instruction (execution := model) (rowWriteOp frame.arrays.c row t))

/-- One actual nonexceptional affine addition consumes its already-inverted denominator. -/
def extendRow (seed row destination : Fin length) : Circuit model ctx ctx :=
  let x := rowRead frame.arrays.x row
  let y := rowRead frame.arrays.y row
  let bx := rowRead frame.arrays.x seed
  let baseY := rowRead frame.arrays.y seed
  Circuit.forRange 10 ![
    Field.Native.Shared.subIntoWord baseY y frame.modulus frame.work.temporary,
    scopedMultiply t (rowRead frame.arrays.c row) modulus frame.work.slope,
    scopedMultiply s s modulus frame.work.temporary,
    Field.Native.Shared.subIntoWord t x frame.modulus frame.work.temporary,
    Field.Native.Shared.subIntoWord t bx frame.modulus frame.work.temporary,
    Field.Native.Shared.subIntoWord x t frame.modulus frame.work.product,
    scopedMultiply s p modulus frame.work.product,
    Field.Native.Shared.subIntoWord p y frame.modulus frame.work.product,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x destination t),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y destination p)]

/-- Prepare exactly -2y for the final shared tangent-denominator batch. -/
def tangentDenominatorRow (row : Fin length) : Circuit model ctx ctx :=
  let y := rowRead frame.arrays.y row
  Circuit.forRange 3 ![
    Field.Native.Shared.addIntoWord y y modulus frame.work.product,
    Field.Native.Shared.subIntoWord frame.zero p frame.modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.c row t)]

/-- The five final columns replace only data whose last use has already occurred. -/
def finishRow (row : Fin length) : Circuit model ctx ctx :=
  let x := rowRead frame.arrays.x row
  let y := rowRead frame.arrays.y row
  Circuit.forRange 15 ![
    scopedMultiply x x modulus frame.work.temporary,
    Field.Native.Shared.addIntoWord t t modulus frame.work.product,
    Field.Native.Shared.addIntoWord p t modulus frame.work.product,
    Field.Native.Shared.addIntoWord p frame.curveA modulus frame.work.product,
    scopedMultiply p (rowRead frame.arrays.c row) modulus frame.work.slope,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.d row s),
    Field.Native.Shared.addIntoWord x x modulus frame.work.temporary,
    Field.Native.Shared.addIntoWord t x modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.c row t),
    Field.Native.Shared.addIntoWord x frame.one modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.e row t),
    Field.Native.Shared.subIntoWord frame.zero x frame.modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x row t),
    Field.Native.Shared.subIntoWord frame.zero y frame.modulus frame.work.temporary,
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y row t)]

/-- The identity address receives zero in all five real columns, including the x+1 table. -/
def clearIdentityRow (row : Fin length) : Circuit model ctx ctx :=
  Circuit.forRange 5 ![
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.c row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.d row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.e row frame.zero)]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
