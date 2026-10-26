/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Blocks
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Framing

/-!
# Consecutive blocks of the original two-array doubling

Seven original scalar slots prepare the slope, six scalar slots compute
the two result coordinates, then two structural writes overwrite the
supplied destinations. This grouping retains the complete original
chronological Store and permits the source and destination row to coincide.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "i" => wordRead frame.work.inverse
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- Actual original slope-preparation slots, including the paid raw coefficient. -/
def slopeInstructions (source : Fin length) : Fin 7 → RowInstruction ctx width length :=
  let x := rowRead frame.x source
  let y := rowRead frame.y source
  ![.add y y frame.work.product,
    .coefficient p frame.work.inverse,
    .multiply x x frame.work.temporary,
    .add t t frame.work.product,
    .add p t frame.work.product,
    .add p frame.curveA frame.work.product,
    .multiply p i frame.work.slope]

/-- Actual six scalar slots computing both coordinates before either array write. -/
def resultInstructions (source : Fin length) : Fin 6 → RowInstruction ctx width length :=
  let x := rowRead frame.x source
  let y := rowRead frame.y source
  ![.add x x frame.work.product,
    .multiply s s frame.work.temporary,
    .sub t p frame.work.product,
    .sub x p frame.work.temporary,
    .multiply s t frame.work.temporary,
    .sub t y frame.work.temporary]

/-- The two original destination writes read already-computed scalar words. -/
def writeInstructions (destination : Fin length) : Fin 2 → RowInstruction ctx width length :=
  ![.write frame.x destination p, .write frame.y destination t]

/-- Exact total Store of the original first seven slots. -/
def slopeStore (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 7 (frame.slopeInstructions source) store

/-- Exact total Store of the original next six slots. -/
def resultStore (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 6 (frame.resultInstructions source) store

/-- Exact total Store of the two original array overwrites. -/
def writeStore (spec : ModulusSpec width) (destination : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 2 (frame.writeInstructions destination) store

/-- Exact total Store of all fifteen original paid doubling slots. -/
def doubleStore (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 15 (frame.instructions source destination) store

/-- Grouping introduces no slot, read, write, or extra storage. -/
lemma doubleStore_eq_blocks (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) :
    frame.doubleStore spec source destination store =
      frame.writeStore spec destination
        (frame.resultStore spec source (frame.slopeStore spec source store)) := by
  have slots : List.ofFn (frame.instructions source destination) =
      List.ofFn (frame.slopeInstructions source) ++
        (List.ofFn (frame.resultInstructions source) ++
          List.ofFn (frame.writeInstructions destination)) := rfl
  unfold doubleStore slopeStore resultStore writeStore
  simp only [RowInstruction.updates_eq_foldl]
  rw [slots, List.foldl_append, List.foldl_append]

/-- Reads outside the actual four scalar outputs survive the slope block. -/
lemma slopeStore_read_other (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (slopeFree : frame.work.slope.key ∉ observed.storageKeys) :
    (frame.slopeStore spec source store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;>
    first | exact productFree | exact inverseFree | exact temporaryFree | exact slopeFree

/-- Reads outside the actual product and temporary outputs survive the result block. -/
lemma resultStore_read_other (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.resultStore spec source store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact productFree | exact temporaryFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
