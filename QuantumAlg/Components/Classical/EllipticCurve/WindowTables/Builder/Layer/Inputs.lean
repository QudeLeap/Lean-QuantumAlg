/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Inputs.Rows
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Original loaded inputs through each actual complete binary layer

Each original stage retains the same loaded modulus and five protected
structural input words. The exact read equalities compose through the
actual returned Stores, including the original first empty batch.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The original denominator traversal preserves every original loaded input reading. -/
lemma layerDenominatorsRecord_originalInputs (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1 (frame.layerDenominatorsRecord level environment before).1.1 :=
  Circuit.forRangeRecord_invariant (layerCount level)
    (fun index => frame.denominatorRow (layerSeed window level) (oldRow level index))
    (fun index => Circuit.preserveHiddenRecord
      (frame.denominatorRecord (layerSeed window level) (oldRow level index) environment))
    (fun _ current => OriginalInputs frame before.1 current.1)
    (fun _index current established => OriginalInputs.trans frame before.1 current.1 _ established
      (frame.denominatorRecord_originalInputs _ _ environment current.1))
    before (OriginalInputs.refl frame before.1)

/-- The original secant traversal preserves every original loaded input reading. -/
lemma layerExtensionsRecord_originalInputs (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1 (frame.layerExtensionsRecord spec level environment before).1.1 :=
  Circuit.forRangeRecord_invariant (layerCount level)
    (fun index => frame.extendRow (layerSeed window level) (oldRow level index)
      (newRow level index))
    (fun index => frame.extendRecord spec (layerSeed window level) (oldRow level index)
      (newRow level index) environment)
    (fun _ current => OriginalInputs frame before.1 current.1)
    (fun _index current established => OriginalInputs.trans frame before.1 current.1 _ established
      (frame.extendRecord_originalInputs spec _ _ _ environment current))
    before (OriginalInputs.refl frame before.1)

attribute [local irreducible] prepareSeedRecord layerDenominatorsRecord layerExtensionsRecord
attribute [local irreducible] BatchFrame.valueRecord

/-- Exact original input readings survive the same actual four-stage layer record. -/
lemma layerRecord_originalInputs (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1 (frame.layerRecord spec level environment before).1.1 := by
  let seeded := (frame.prepareSeedRecord spec level environment before).1
  let denominators := (frame.layerDenominatorsRecord level environment seeded).1
  let inverted := (frame.batch.valueRecord spec (layerCount level) (layerFits level)
    environment denominators).1
  change OriginalInputs frame before.1
    (frame.layerExtensionsRecord spec level environment inverted).1.1
  exact OriginalInputs.trans frame before.1 seeded.1 _
    (frame.prepareSeedRecord_originalInputs spec level environment before)
    (OriginalInputs.trans frame seeded.1 denominators.1 _
      (frame.layerDenominatorsRecord_originalInputs level environment seeded)
      (OriginalInputs.trans frame denominators.1 inverted.1 _
        (frame.batchRecord_originalInputs spec (layerCount level) (layerFits level)
          environment denominators)
        (frame.layerExtensionsRecord_originalInputs spec level environment inverted)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
