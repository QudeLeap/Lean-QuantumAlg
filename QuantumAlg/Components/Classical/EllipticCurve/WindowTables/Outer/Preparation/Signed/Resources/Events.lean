/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Resources.Events
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction

/-!
# Independent complete native pool for the original signed preparation

The original constant loaders, two nominal point unpacks, paid field
subtraction and both complete base families keep their native event labels.
The allowance depends only on widths and the supplied public modulus spec;
it is independent of actual paths, Store values and borrowed input placement.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

/-- Independent native coordinates for the original modulus, coefficient and one loaders. -/
def initializationEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ConstantWord.envelope model (width + 1) +
    (ConstantWord.envelope model width +
      ResourcePool.singleton (ConstantWord.incrementEvent model width))

/-- One actual original nominal point unpack retains its width-indexed native coordinate. -/
def unpackEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.nominalEncoding (.unpackEllipticCurvePoint width))))

/-- Independent complete finite native allowance for both actual signed seventeen-row families. -/
def envelope (model : ExecutionModel) [BitWord.Selected model] {width : Nat}
    (spec : ModulusSpec width) : ResourcePool model :=
  initializationEnvelope model width +
    (unpackEnvelope model width + (unpackEnvelope model width +
      (ResourcePool.ofList (Field.Native.subtractionTrace model spec) +
        (CoordinateFrame.basesEnvelope model 34 16 spec +
          CoordinateFrame.basesEnvelope model 34 16 spec))))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma initialization_pool_le (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat)
    (path : (frame.initializeConstants (model := model) spec coefficient).Path) :
    (frame.initializeConstants (model := model) spec coefficient).resourcePool path ≤
      initializationEnvelope model width := by
  have increment :
      (BitWord.instruction (execution := model) (ConstantWord.incrementOp frame.one)).resourcePool
        path.2.2 = ResourcePool.singleton (ConstantWord.incrementEvent model width) := by
    rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
    rfl
  exact Accounting.seq_pool_le _ _ _ _ path
    (ConstantWord.constantWord_pool_le frame.modulus spec.modulus path.1)
    (Accounting.seq_pool_le _ _ _ _ path.2
      (ConstantWord.constantWord_pool_le frame.curveA coefficient path.2.1) increment.le)

private lemma unpack_pool (input : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointEquality.RawPointShape width))
    (path : (BitWord.instruction (execution := model)
      (.unpackEllipticCurvePoint width ctx input output)).Path) :
    (BitWord.instruction (execution := model)
      (.unpackEllipticCurvePoint width ctx input output)).resourcePool path =
      unpackEnvelope model width := by
  rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma pairedBases_pool_le (frame : Frame ctx width) (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (path : (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).Path) :
    (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).resourcePool
      path ≤ CoordinateFrame.basesEnvelope model 34 16 spec +
        CoordinateFrame.basesEnvelope model 34 16 spec := by
  exact Accounting.seq_pool_le _ _ _ _ path
    (frame.coordinates.prepareBasesAt_pool_le spec firstX firstY (@firstBaseRows 16) path.1)
    (frame.coordinates.prepareBasesAt_pool_le spec secondX secondY (@secondBaseRows 16) path.2)

/-- Every actual signed-prefix path obeys the complete independent native-event allowance. -/
lemma prepare_pool_le (frame : Frame ctx width) (spec : ModulusSpec width)
    (coefficient : Nat) (base target : CInputRef ctx (PointShape width))
    (path : (prepare (model := model) frame spec coefficient base target).Path) :
    (prepare (model := model) frame spec coefficient base target).resourcePool path ≤
      envelope model spec := by
  unfold prepare at path ⊢
  apply Accounting.seq_pool_le _ _ _ _ path
    (initialization_pool_le frame spec coefficient path.1)
  apply withCellsFrom_property (Transport.id ctx) (scratchShapes width)
    (fun cells _ lift _ =>
      let scratch := scratchOfCells cells
      let localFrame := frame.transport lift
      .seq (BitWord.instruction (execution := model)
        (.unpackEllipticCurvePoint width _ (lift.liftInput base) scratch.rawBase))
        (.seq (BitWord.instruction (execution := model)
          (.unpackEllipticCurvePoint width _ (lift.liftInput target) scratch.rawTarget))
          (.seq (Field.Native.subIntoWord spec (.storage localFrame.zero.toCStorageRef)
            (rawY scratch.rawTarget) scratch.signedY)
            (localFrame.preparePairedBases spec (rawX scratch.rawBase) (rawY scratch.rawBase)
              (rawX scratch.rawTarget) (.storage scratch.signedY.toCStorageRef)))))
    (fun _ code => ∀ selected, code.resourcePool selected ≤
      unpackEnvelope model width + (unpackEnvelope model width +
        (ResourcePool.ofList (Field.Native.subtractionTrace model spec) +
          (CoordinateFrame.basesEnvelope model 34 16 spec +
            CoordinateFrame.basesEnvelope model 34 16 spec))))
    (fun _ _ _ _ _ available => available) ?_ path.2
  intro inner cells distinct lift separated selected
  exact Accounting.seq_pool_le _ _ _ _ selected (unpack_pool _ _ selected.1).le
    (Accounting.seq_pool_le _ _ _ _ selected.2 (unpack_pool _ _ selected.2.1).le
      (Accounting.seq_pool_le _ _ _ _ selected.2.2
        (Field.Native.subIntoWord_resourcePool spec _ _ _ selected.2.2.1).le
        (pairedBases_pool_le _ spec _ _ _ _ selected.2.2.2)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
