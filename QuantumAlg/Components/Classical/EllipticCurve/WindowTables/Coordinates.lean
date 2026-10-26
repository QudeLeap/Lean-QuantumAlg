/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Sequence

/-!
# Actual doubling with only the two existing coordinate arrays

The original fifteen paid doubling slots use two coordinate arrays, four
working words and the actual shared modulus/curve coefficient. No C/D/E
arrays are needed. This is also the literal doubling used inside the full
five-array builder, so small window-base arrays can reuse it directly.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower ClassicalAlgorithms.Modular

variable {kind : ProblemKind}

/-- Existing storage sufficient for the original paid affine-doubling slots. -/
structure CoordinateFrame (ctx : RuntimeCtx kind) (width length : Nat) where
  x : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  y : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  separate : x.key ≠ y.key
  work : Work ctx width
  modulus : CWriteRef ctx (.unsignedWord (width + 1))
  curveA : CInputRef ctx (.unsignedWord width)
  protectedCoefficient : ∀ key ∈ [x.key, y.key, work.product.key, work.inverse.key,
    work.temporary.key, work.slope.key], key ∉ curveA.storageKeys

namespace CoordinateFrame

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx kind} {width length : Nat} (frame : CoordinateFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "i" => wordRead frame.work.inverse
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- Literal original shared-modulus doubling slots; both coordinate writes occur last. -/
def instructions (source destination : Fin length) : Fin 15 → RowInstruction ctx width length :=
  let x := rowRead frame.x source
  let y := rowRead frame.y source
  ![.add y y frame.work.product,
    .coefficient p frame.work.inverse,
    .multiply x x frame.work.temporary,
    .add t t frame.work.product,
    .add p t frame.work.product,
    .add p frame.curveA frame.work.product,
    .multiply p i frame.work.slope,
    .add x x frame.work.product,
    .multiply s s frame.work.temporary,
    .sub t p frame.work.product,
    .sub x p frame.work.temporary,
    .multiply s t frame.work.temporary,
    .sub t y frame.work.temporary,
    .write frame.x destination p,
    .write frame.y destination t]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : CoordinateFrame ctx width length)

/-- The original paid doubling on the supplied existing two-array storage. -/
def doubleCircuit (spec : ModulusSpec width) (source destination : Fin length) :
    Circuit model ctx ctx :=
  Circuit.forRange 15 (fun index => (frame.instructions source destination index).circuit spec
    frame.modulus)

/-- Exact original chronological Store/path record, including the one real XGCD coefficient. -/
def doubleRecord (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.doubleCircuit (model := model) spec source destination).Path :=
  RowInstruction.rangeRecord spec frame.modulus environment 15
    (frame.instructions source destination)

/-- The complete actual doubling retains every incoming history and arbitrary Reference block. -/
lemma doubleCircuit_execute (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.doubleCircuit (model := model) spec source destination).execute environment Reference
      state = state.mapClassical (fun entry =>
        let result := frame.doubleRecord spec source destination environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  RowInstruction.range_execute spec frame.modulus environment 15
    (frame.instructions source destination) Reference state

end

end CoordinateFrame

namespace TableFrame

variable {ctx : RuntimeCtx kind} {width length : Nat}

/-- The full builder's original doubling uses exactly this existing coordinate-only subframe. -/
def coordinates (frame : TableFrame ctx width length) : CoordinateFrame ctx width length where
  x := frame.arrays.x
  y := frame.arrays.y
  separate := by
    have absent := (List.nodup_cons.mp frame.arrays.distinct).1
    exact fun same => absent (by simp [same])
  work := frame.work
  modulus := frame.modulus
  curveA := frame.curveA
  protectedCoefficient := by
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact frame.protectedReads frame.curveA (by simp) _ (by simp)

end TableFrame

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
