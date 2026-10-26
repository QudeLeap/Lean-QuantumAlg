/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Unpack.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Preservation

/-! # Caller reads preserved by the actual signed-row callback -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalAlgorithms.Modular

noncomputable section
variable {model : ExecutionModel} [BitWord.Selected model] {width : Nat}

/-- The two actual base-family records preserve any structural read outside their outputs. -/
lemma pairedBasesRecord_read_other {ctx : RuntimeCtx model.kind}
    (frame : Frame ctx width) (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : OutputFree frame.coordinates observed) :
    (frame.pairedBasesRecord spec firstX firstY secondX secondY environment before).1.1.read
      observed = before.1.read observed := by
  rw [frame.pairedBasesRecord_state]
  exact (bases_read frame.coordinates spec environment observed free secondX secondY
    (@secondBaseRows 16) _).trans
      (bases_read frame.coordinates spec environment observed free firstX firstY
        (@firstBaseRows 16) before)

omit [BitWord.Selected model] in
/-- Transport keeps every actual output key and every original input support. -/
lemma outputFree_transport {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (lift : Transport outer inner)
    {shape : CShape} (observed : CInputRef outer shape)
    (free : OutputFree frame.coordinates observed) :
    OutputFree (frame.transport lift).coordinates (lift.liftInput observed) := by
  intro key member
  rw [lift.liftInput_storageKeys]
  apply free key
  simpa only [Frame.coordinates, Frame.work, Frame.transport, Transport.liftWrite_key]
    using member

/-- Unpacking, signed subtraction and both table families preserve each untouched caller read. -/
lemma callbackRecord_read_other {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment) (before : Store inner × model.HiddenState)
    {shape : CShape} (observed : CInputRef outer shape)
    (free : OutputFree frame.coordinates observed) :
    (callbackRecord frame spec base target cells distinct lift separated
      environment before).1.1.read (lift.liftInput observed) =
        before.1.read (lift.liftInput observed) := by
  let scratch := scratchOfCells cells
  let localFrame := frame.transport lift
  let unpacked := twoUnpackStore (lift.liftInput base) (lift.liftInput target)
    scratch.rawBase scratch.rawTarget before.1
  have avoids := scratch_avoids_original lift cells separated observed
  rw [callbackRecord_store]
  rw [pairedBasesRecord_read_other _ _ _ _ _ _ _ _ _
    (outputFree_transport frame lift observed free)]
  rw [Field.Native.subIntoWordStep_read_other (environment := environment)
    spec (.storage localFrame.zero.toCStorageRef) (rawY scratch.rawTarget)
    scratch.signedY unpacked (lift.liftInput observed) avoids.2.2]
  exact twoUnpackStore_read_other (lift.liftInput base) (lift.liftInput target)
    scratch.rawBase scratch.rawTarget before.1 (lift.liftInput observed)
    avoids.1 avoids.2.1

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
