/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Program
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Unpack.Record
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-! Complete Store, hidden state, History and Reference semantics of paid signed rows. -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalRoutines.EllipticCurve QuantumAlg.ClassicalAlgorithms.Modular

noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α
variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The literal subtraction and paired-base tail of `prepare`'s callback. -/
def signedTail (frame : WindowTables.Outer.Frame ctx width)
    (spec : ModulusSpec width) (scratch : Scratch ctx width) : Circuit model ctx ctx :=
  .seq
    (Field.Native.subIntoWord spec
      (.storage frame.zero.toCStorageRef)
      (rawY scratch.rawTarget) scratch.signedY)
    (frame.preparePairedBases spec
      (rawX scratch.rawBase) (rawY scratch.rawBase)
      (rawX scratch.rawTarget)
      (.storage scratch.signedY.toCStorageRef))

/-- Actual arithmetic and paired-base updates on the same intermediate state. -/
def signedTailRecord (frame : WindowTables.Outer.Frame ctx width)
    (spec : ModulusSpec width) (scratch : Scratch ctx width)
    (environment : model.Environment)
    (before : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) ×
      (signedTail (model := model) frame spec scratch).Path :=
  Circuit.sequenceRecord (model := model)
    (Field.Native.subIntoWord (model := model) spec
      (.storage frame.zero.toCStorageRef)
      (rawY scratch.rawTarget) scratch.signedY)
    (frame.preparePairedBases (model := model) spec
      (rawX scratch.rawBase) (rawY scratch.rawBase)
      (rawX scratch.rawTarget)
      (.storage scratch.signedY.toCStorageRef))
    (Circuit.preserveHiddenRecord (model := model)
      (Field.Native.subIntoWordStep (model := model) (environment := environment)
        spec (.storage frame.zero.toCStorageRef)
        (rawY scratch.rawTarget) scratch.signedY))
    (frame.pairedBasesRecord (model := model) spec
      (rawX scratch.rawBase) (rawY scratch.rawBase)
      (rawX scratch.rawTarget)
      (.storage scratch.signedY.toCStorageRef) environment) before

/-- The same two tail circuits preserve arbitrary input Reference and History. -/
lemma signedTail_execute (frame : WindowTables.Outer.Frame ctx width)
    (spec : ModulusSpec width) (scratch : Scratch ctx width)
    (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference
      (model.HiddenState × History)) :
    (signedTail (model := model) frame spec scratch).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := signedTailRecord (model := model) frame spec scratch environment
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold signedTail signedTailRecord
  apply Circuit.execute_sequenceRecord
  · intro reference history _ initial
    exact (Field.Native.subIntoWord_execute (model := model)
      (environment := environment) spec
      (.storage frame.zero.toCStorageRef)
      (rawY scratch.rawTarget) scratch.signedY reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact frame.preparePairedBases_execute spec
      (rawX scratch.rawBase) (rawY scratch.rawBase)
      (rawX scratch.rawTarget)
      (.storage scratch.signedY.toCStorageRef) environment reference initial


/-- The exact callback body of the existing paid signed-row preparation. -/
def callbackBody {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width)
    (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (_distinct : cells.Distinct)
    (lift : Transport outer inner) (_separated : cells.TransportSeparated lift) :
    Circuit model inner inner :=
  let scratch := scratchOfCells cells
  let localFrame := frame.transport lift
  .seq
    (BitWord.instruction (execution := model)
      (.unpackEllipticCurvePoint width inner (lift.liftInput base) scratch.rawBase))
    (.seq
      (BitWord.instruction (execution := model)
        (.unpackEllipticCurvePoint width inner (lift.liftInput target) scratch.rawTarget))
      (.seq
        (Field.Native.subIntoWord spec
          (.storage localFrame.zero.toCStorageRef)
          (rawY scratch.rawTarget) scratch.signedY)
        (localFrame.preparePairedBases spec
          (rawX scratch.rawBase) (rawY scratch.rawBase)
          (rawX scratch.rawTarget)
          (.storage scratch.signedY.toCStorageRef))))

/-- The named body is definitionally the callback of the unchanged program. -/
lemma prepare_eq_named_callback {ctx : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame ctx width)
    (spec : ModulusSpec width) (coefficient : Nat)
    (base target : CInputRef ctx (PointShape width)) :
    prepare (model := model) frame spec coefficient base target =
      .seq (frame.initializeConstants spec coefficient)
        (withCells (model := model) ctx (scratchShapes width) fun
          {_inner} cells distinct lift separated =>
            callbackBody (model := model) frame spec base target
              cells distinct lift separated) := by
  rfl

/-- The callback's Store, service state and original right-associated path. -/
def callbackRecord {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width)
    (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment)
    (before : Store inner × model.HiddenState) :
    (Store inner × model.HiddenState) ×
      (callbackBody (model := model) frame spec base target
        cells distinct lift separated).Path :=
  WindowTables.Outer.Preparation.twoUnpackThenRecord (model := model)
    (lift.liftInput base) (lift.liftInput target)
    (scratchOfCells cells).rawBase (scratchOfCells cells).rawTarget
    (signedTail (model := model) (frame.transport lift) spec (scratchOfCells cells))
    (signedTailRecord (model := model) (frame.transport lift) spec
      (scratchOfCells cells) environment) before

/-- Every quantum/reference block follows that same actual complete callback record. -/
lemma callbackBody_execute {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width)
    (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State inner Reference
      (model.HiddenState × History)) :
    (callbackBody (model := model) frame spec base target
      cells distinct lift separated).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := callbackRecord (model := model) frame spec base target
          cells distinct lift separated environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact WindowTables.Outer.Preparation.twoUnpackThen_execute
    (model := model) (lift.liftInput base) (lift.liftInput target)
    (scratchOfCells cells).rawBase (scratchOfCells cells).rawTarget
    (signedTail (model := model) (frame.transport lift) spec (scratchOfCells cells))
    environment
    (signedTailRecord (model := model) (frame.transport lift) spec
      (scratchOfCells cells) environment)
    (signedTail_execute (model := model) (frame.transport lift) spec
      (scratchOfCells cells) environment) Reference state


/-- The actual callback uses the two real unpack updates and one paid signed-Y update. -/
lemma callbackRecord_store {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width) (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment)
    (before : Store inner × model.HiddenState) :
    let scratch := scratchOfCells cells
    let localFrame := frame.transport lift
    let unpacked := WindowTables.Outer.Preparation.twoUnpackStore
      (lift.liftInput base) (lift.liftInput target)
      scratch.rawBase scratch.rawTarget before.1
    let afterSub :=
      (Field.Native.subIntoWordStep (model := model) (environment := environment)
        spec (.storage localFrame.zero.toCStorageRef)
        (rawY scratch.rawTarget) scratch.signedY unpacked).1
    (callbackRecord (model := model) frame spec base target cells distinct lift
      separated environment before).1.1 =
      (localFrame.pairedBasesRecord spec
        (rawX scratch.rawBase) (rawY scratch.rawBase)
        (rawX scratch.rawTarget) (.storage scratch.signedY.toCStorageRef)
        environment (afterSub, before.2)).1.1 := by
  dsimp only
  unfold callbackRecord
  rw [WindowTables.Outer.Preparation.twoUnpackThenRecord_state]
  unfold signedTailRecord
  rw [Circuit.sequenceRecord_store]
  rfl


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
