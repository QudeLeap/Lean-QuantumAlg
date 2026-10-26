/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Preservation

/-!
# Both original point families in the same actual returned Store

The second paid base preparation consumes the first preparation's actual
Store and service state. Its writes preserve every first-family row.
The original second input is retained through the first preparation by
structural physical separation from the same six actual output cells.
Both original prime-order point domains are unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

open Execution ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

attribute [local irreducible] CoordinateFrame.prepareBasesAtRecord pairedBasesRecord

/-- Both actual disjoint families have their original power-of-two point values simultaneously. -/
lemma pairedBasesRecord_values (curve : CurveSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (firstPoint secondPoint : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf firstPoint = order) (secondOrder : addOrderOf secondPoint = order)
    (loaded : before.1.read (wordRead frame.coordinates.modulus) =
      .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.coordinates.curveA).toNat : ZMod curve.field.modulus) =
      curve.curve.a)
    (firstYFree : frame.coordinates.x.key ∉ firstY.storageKeys)
    (secondXFree : Preparation.OutputFree frame.coordinates secondX)
    (secondYFree : Preparation.OutputFree frame.coordinates secondY)
    (firstInput : CoordinateValue curve (before.1.read firstX) (before.1.read firstY) firstPoint)
    (secondInput : CoordinateValue curve (before.1.read secondX)
      (before.1.read secondY) secondPoint) :
    let returned := (frame.pairedBasesRecord curve.field firstX firstY secondX secondY
      environment before).1.1
    returned.read (wordRead frame.coordinates.modulus) = before.1.read
        (wordRead frame.coordinates.modulus) ∧
      returned.read frame.coordinates.curveA = before.1.read frame.coordinates.curveA ∧
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
        ((2 ^ (16 * index.val)) • firstPoint)) ∧
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
        ((2 ^ (16 * index.val)) • secondPoint)) := by
  let first := frame.coordinates.prepareBasesAtRecord curve.field firstX firstY
    (@firstBaseRows 16) environment before
  have firstValues := frame.coordinates.prepareBasesAtRecord_values curve firstX firstY
    (@firstBaseRows 16) firstBaseRows_injective environment before firstPoint order prime large
    firstOrder loaded curveValue firstYFree firstInput
  have secondXRead := Preparation.bases_read frame.coordinates curve.field environment
    secondX secondXFree firstX firstY (@firstBaseRows 16) before
  have secondYRead := Preparation.bases_read frame.coordinates curve.field environment
    secondY secondYFree firstX firstY (@firstBaseRows 16) before
  have retainedInput : CoordinateValue curve (first.1.1.read secondX) (first.1.1.read secondY)
      secondPoint := by
    rw [secondXRead, secondYRead]
    exact secondInput
  have secondValues := frame.coordinates.prepareBasesAtRecord_values curve secondX secondY
    (@secondBaseRows 16) secondBaseRows_injective environment first.1 secondPoint order prime large
    secondOrder (firstValues.1.trans loaded) (by rw [firstValues.2.1]; exact curveValue)
    (secondYFree _ (by simp)) retainedInput
  dsimp only
  rw [frame.pairedBasesRecord_state]
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨secondValues.1.trans firstValues.1, secondValues.2.1.trans firstValues.2.1,
    ?_, secondValues.2.2⟩
  intro index
  have xRetained := frame.coordinates.prepareBasesAtRecord_read_outside curve.field secondX secondY
    (@secondBaseRows 16) environment first.1 frame.coordinates.x (firstBaseRows index)
    (fun other => firstBaseRows_ne_secondBaseRows index other)
  have yRetained := frame.coordinates.prepareBasesAtRecord_read_outside curve.field secondX secondY
    (@secondBaseRows 16) environment first.1 frame.coordinates.y (firstBaseRows index)
    (fun other => firstBaseRows_ne_secondBaseRows index other)
  rw [xRetained, yRetained]
  exact firstValues.2.2 index

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame
