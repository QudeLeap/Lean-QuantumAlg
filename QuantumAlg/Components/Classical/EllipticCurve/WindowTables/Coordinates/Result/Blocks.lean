/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Slope

/-!
# Two consecutive halves of the actual scalar coordinate result block

Three slots compute the new x in the product word. The final three slots
compute the new y in the temporary word while preserving that product.
Only grouping changes; every actual input and overwrite remains in order.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- The first three original scalar-result slots compute the new x word. -/
def resultFirstInstructions (source : Fin length) : Fin 3 → RowInstruction ctx width length :=
  let x := rowRead frame.x source
  ![.add x x frame.work.product, .multiply s s frame.work.temporary,
    .sub t p frame.work.product]

/-- The last three original scalar-result slots compute the new y word. -/
def resultLastInstructions (source : Fin length) : Fin 3 → RowInstruction ctx width length :=
  let x := rowRead frame.x source
  let y := rowRead frame.y source
  ![.sub x p frame.work.temporary, .multiply s t frame.work.temporary,
    .sub t y frame.work.temporary]

/-- Actual Store of the first three original result slots. -/
def resultFirstStore (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 3 (frame.resultFirstInstructions source) store

/-- Actual Store of the last three original result slots. -/
def resultLastStore (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 3 (frame.resultLastInstructions source) store

/-- The shared intermediate Store is exactly the original six-slot chronological boundary. -/
lemma resultStore_eq_blocks (spec : ModulusSpec width) (source : Fin length) (store : Store ctx) :
    frame.resultStore spec source store =
      frame.resultLastStore spec source (frame.resultFirstStore spec source store) := by
  have slots : List.ofFn (frame.resultInstructions source) =
      List.ofFn (frame.resultFirstInstructions source) ++
        List.ofFn (frame.resultLastInstructions source) := rfl
  unfold resultStore resultFirstStore resultLastStore
  simp only [RowInstruction.updates_eq_foldl]
  rw [slots, List.foldl_append]

/-- Exact reads outside the two first-half scalar outputs survive. -/
lemma resultFirstStore_read_other (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.resultFirstStore spec source store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact productFree | exact temporaryFree

/-- The last half changes only the original temporary scalar. -/
lemma resultLastStore_read_other (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.resultLastStore spec source store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> exact temporaryFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
