/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Words

/-!
# Exact complete Store and record of the original ten-slot secant row

The same actual slope-prefix Store feeds the original new-x calculation,
the unchanged coordinate suffix and both physical destination writes.
The C word is read from the original actual batch output; no inverse or
table value is inserted into the program constructor.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Both real destinations receive precisely the original secant finite-word coordinate pair. -/
lemma extendStore_read_values (spec : ModulusSpec width) (seed row destination : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    let values := extendWords spec (store.read (rowRead frame.arrays.x row))
      (store.read (rowRead frame.arrays.y row)) (store.read (rowRead frame.arrays.x seed))
      (store.read (rowRead frame.arrays.y seed)) (store.read (rowRead frame.arrays.c row))
    (frame.extendStore spec seed row destination store).read (rowRead frame.arrays.x destination) =
        values.1 ∧
      (frame.extendStore spec seed row destination store).read
        (rowRead frame.arrays.y destination) = values.2 := by
  let alternate := frame.coordinates.swapProductTemporary
  let first := frame.extendFirstStore spec seed row store
  let second := frame.extendXStore spec seed row first
  have firstInputs : ExtendInputReads frame seed row store first :=
    frame.extendFirstStore_inputReads spec seed row store
  have secondInputs : ExtendInputReads frame seed row first second :=
    frame.extendXStore_inputReads spec seed row first
  have originalInputs := ExtendInputReads.trans frame seed row store first second
    firstInputs secondInputs
  have firstLoaded := firstInputs.modulus.trans loaded
  have secondLoaded := originalInputs.modulus.trans loaded
  have newX := frame.extendXStore_read_temporary spec seed row first firstLoaded
  have originalSlope : second.read (wordRead frame.work.slope) =
      multiplyValue (subValue (store.read (rowRead frame.arrays.y seed))
        (store.read (rowRead frame.arrays.y row)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.c row)) (.unsignedWord spec.extendedWord) :=
    (frame.extendXStore_read_other spec seed row first (wordRead frame.work.slope) (by
      change frame.work.temporary.key ∉ [frame.work.slope.key]
      simpa [Work.word] using frame.work.word_key_ne 2 3 (by decide))).trans
        (frame.extendFirstStore_read_slope spec seed row store loaded)
  constructor
  · rw [frame.extendStore_eq_blocks]
    change (alternate.writeStore spec destination
      (alternate.resultLastStore spec row second)).read (rowRead alternate.x destination) = _
    rw [alternate.writeStore_read_x]
    change (alternate.resultLastStore spec row second).read (wordRead frame.work.temporary) = _
    rw [alternate.resultLastStore_read_other spec row second (wordRead frame.work.temporary) (by
      change frame.work.product.key ∉ [frame.work.temporary.key]
      simpa [Work.word] using frame.work.word_key_ne 0 2 (by decide)), newX,
      firstInputs.x, firstInputs.baseX,
      frame.extendFirstStore_read_slope spec seed row store loaded]
    rfl
  · rw [frame.extendStore_eq_blocks]
    change (alternate.writeStore spec destination
      (alternate.resultLastStore spec row second)).read (rowRead alternate.y destination) = _
    rw [alternate.writeStore_read_y,
      alternate.resultLastStore_read_temporary spec row second secondLoaded]
    change subValue (multiplyValue (second.read (wordRead frame.work.slope))
      (subValue (second.read (rowRead frame.arrays.x row))
        (second.read (wordRead frame.work.temporary)) (.unsignedWord spec.extendedWord))
        (.unsignedWord spec.extendedWord)) (second.read (rowRead frame.arrays.y row))
        (.unsignedWord spec.extendedWord) = _
    rw [originalInputs.x, originalInputs.y, originalSlope, newX,
      firstInputs.x, firstInputs.baseX,
      frame.extendFirstStore_read_slope spec seed row store loaded]
    rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- Actual complete chronological record of the unchanged ten paid secant slots. -/
def extendRecord (spec : ModulusSpec width) (seed row destination : Fin length)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.extendRow (model := model) seed row destination).Path :=
  RowInstruction.rangeRecord spec frame.modulus environment 10
    (frame.extendInstructions seed row destination)

/-- The actual complete record has exactly the total finite-word Store used in the value proof. -/
lemma extendRecord_store (spec : ModulusSpec width) (seed row destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.extendRecord spec seed row destination environment before).1.1 =
      frame.extendStore spec seed row destination before.1 :=
  RowInstruction.rangeRecord_store spec frame.modulus environment 10
    (frame.extendInstructions seed row destination) before

/-- Every original history/reference block follows that same actual secant overwrite record. -/
lemma extendRow_execute (spec : ModulusSpec width) (seed row destination : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.extendRow (model := model) seed row destination).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.extendRecord spec seed row destination environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  RowInstruction.range_execute spec frame.modulus environment 10
    (frame.extendInstructions seed row destination) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
