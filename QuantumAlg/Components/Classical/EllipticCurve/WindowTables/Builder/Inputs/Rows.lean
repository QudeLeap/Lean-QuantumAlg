/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Inputs
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Denominator.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Tangent
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Seed

/-!
# Original input readings through each actual table row

Every original row record preserves the widened modulus and the five
protected structural input words. The initial seed uses its actual two
writes; later seeds use the original paid doubling record. These exact
read equalities place no restriction on the incoming working words.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- All original inputs survive the actual fifteen-slot doubling record. -/
lemma doubleRowRecord_originalInputs (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.doubleRowRecord spec source destination environment before).1.1 := by
  apply frame.rowRecord_originalInputs
  intro index
  fin_cases index <;> simp [doubleInstructions, RowInstruction.writtenKey, outputKeys]

/-- All original inputs survive the actual ten-slot secant record. -/
lemma extendRecord_originalInputs (spec : ModulusSpec width) (seed row destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.extendRecord spec seed row destination environment before).1.1 := by
  apply frame.rowRecord_originalInputs
  intro index
  fin_cases index <;> simp [extendInstructions, RowInstruction.writtenKey, outputKeys]

/-- All original inputs survive the three real negative-tangent slots. -/
lemma tangentRecord_originalInputs (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.tangentRecord spec row environment before).1.1 := by
  apply frame.rowRecord_originalInputs
  intro index
  fin_cases index <;> simp [tangentInstructions, RowInstruction.writtenKey, outputKeys]

/-- All original inputs survive the fifteen real final-column slots. -/
lemma finishRecord_originalInputs (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.finishRecord spec row environment before).1.1 := by
  apply frame.rowRecord_originalInputs
  intro index
  fin_cases index <;> simp [finishInstructions, RowInstruction.writtenKey, outputKeys]

/-- All original inputs survive the original shared subtraction and actual C overwrite. -/
lemma denominatorRecord_originalInputs (seed row : Fin length) (environment : model.Environment)
    (before : Store ctx) :
    OriginalInputs frame before (frame.denominatorRecord seed row environment before).1 := by
  refine ⟨?_, ?_⟩
  · exact frame.denominatorRecord_read_other seed row environment before (wordRead frame.modulus)
      (frame.outputKey_modulus_free _ (by simp [outputKeys]))
      (frame.outputKey_modulus_free _ (by simp [outputKeys]))
  · intro input member
    exact frame.denominatorRecord_read_other seed row environment before input
      (frame.outputKey_free _ (by simp [outputKeys]) input member)
      (frame.outputKey_free _ (by simp [outputKeys]) input member)

/-- The initial two actual coordinate writes preserve every original protected input. -/
lemma seedRecord_originalInputs (row : Fin length) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.coordinates.seedRecord (model := model) frame.baseX frame.baseY row before).1.1 := by
  refine ⟨?_, ?_⟩
  · exact frame.coordinates.seedRecord_read_other frame.baseX frame.baseY row before
      (wordRead frame.modulus) (frame.outputKey_modulus_free _ (by simp [outputKeys, coordinates]))
      (frame.outputKey_modulus_free _ (by simp [outputKeys, coordinates]))
  · intro input member
    exact frame.coordinates.seedRecord_read_other frame.baseX frame.baseY row before input
      (frame.outputKey_free _ (by simp [outputKeys, coordinates]) input member)
      (frame.outputKey_free _ (by simp [outputKeys, coordinates]) input member)

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

/-- Either actual public-level seed branch retains the same original loaded inputs. -/
lemma prepareSeedRecord_originalInputs (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.prepareSeedRecord spec level environment before).1.1 := by
  rcases level with ⟨value, bounded⟩
  cases value with
  | zero => exact frame.seedRecord_originalInputs (layerSeed window ⟨0, bounded⟩) before
  | succ value =>
      exact frame.doubleRowRecord_originalInputs spec
        (previousSeed window ⟨value + 1, bounded⟩) (layerSeed window ⟨value + 1, bounded⟩)
        environment before

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
