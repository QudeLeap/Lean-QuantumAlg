/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Correctness
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Actual canonical group coordinates of every positive table address

The original finite traversal advances the proved natural frontier at
each actual binary layer. Every positive final coordinate row represents
its original address times the admitted original point. The loaded inputs
retain their original readings through the same complete actual record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The actual original binary traversal constructs all positive coordinate rows
and retains inputs. -/
lemma coordinateLayersRecord_values (curve : CurveSpec width) (environment : model.Environment)
    (before : Store ctx × model.HiddenState) (point : Point curve) (order : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order)
    (tableFits : 2 ^ window < order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (baseValue : CoordinateValue curve (before.1.read frame.baseX)
      (before.1.read frame.baseY) point) :
    let returned := (frame.coordinateLayersRecord curve.field environment before).1.1
    OriginalInputs frame before.1 returned ∧
      frame.CoordinateRowsValue curve point (2 ^ window) returned := by
  exact Circuit.forRangeRecord_invariant window (frame.layerCircuit curve.field)
    (fun level => frame.layerRecord curve.field level environment)
    (fun processed current => OriginalInputs frame before.1 current.1 ∧
      frame.CoordinateRowsValue curve point (2 ^ processed) current.1)
    (fun level current established => by
      refine ⟨OriginalInputs.trans frame before.1 current.1 _ established.1
        (frame.layerRecord_originalInputs curve.field level environment current), ?_⟩
      apply frame.layerRecord_rowsValue curve level environment current point order prime large
        original tableFits (established.1.modulus.trans loaded)
      · rw [established.1.inputs frame.one (by simp)]
        exact one
      · rw [established.1.inputs frame.curveA (by simp)]
        exact curveValue
      · rw [established.1.inputs frame.baseX (by simp), established.1.inputs frame.baseY (by simp)]
        exact baseValue
      · exact established.2)
    before ⟨OriginalInputs.refl frame before.1,
      frame.coordinateRowsValue_initial curve point before.1⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
