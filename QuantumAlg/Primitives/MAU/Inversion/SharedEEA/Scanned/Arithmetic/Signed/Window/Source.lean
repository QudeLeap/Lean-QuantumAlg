/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Reverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body

/-!
# Exact source order of the complete signed streamed window

The pre-overflow word precedes the descending operand chain. Carry
overflow follows the upward carry word. All six original stages keep
their source order, including the native carry-before-sum inverse pair
[TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow

noncomputable section

open EncodedBit ArithmeticTemplate NumberTheory.SharedEEA

/-- Fused source words restore both signed instructions at their precise source boundaries. -/
def stageWord (width last : Nat) : Stage → List (GateSpec (Scanned.encoding width))
  | .descendingXor => (ArithmeticSigned.nativeWord width .pre last).reverse
  | .carry => ArithmeticSigned.nativeWord width .carry last
  | stage => ArithmeticWindow.stageWord width (last + 1) stage

/-- The six literal native words remain in chronological source order. -/
def sourceWord (width last : Nat) : List (GateSpec (Scanned.encoding width)) :=
  ArithmeticWindow.stages.flatMap (stageWord width last)

private lemma map_low_word (width length : Nat) (fits : length ≤ width + 3)
    (gates : List (GateSpec (Addition.TTK.encoding length))) :
    gates.map (ArithmeticWindow.mapGate width length fits) =
      (gates.map Addition.TTK.withOverflowGate).map (ArithmeticTop.mapGate width length fits) := by
  rw [List.map_map]
  apply congrArg (fun transform => gates.map transform)
  funext gate
  exact (ArithmeticTop.map_lifted width length fits gate).symm

private lemma source_pre (width last : Nat) (fits : last + 1 ≤ width + 3) :
    ArithmeticTop.source width .pre last =
      (if 0 < last then [Addition.TTK.overflowPreGate last] else []).map
        (ArithmeticTop.mapGate width (last + 1) fits) := by
  rw [ArithmeticTop.source, dif_pos (show last < width + 3 by omega)]
  split_ifs
  · rw [List.map_singleton, ArithmeticTop.map_preGate]
  · rfl

private lemma source_carry (width last : Nat) (fits : last + 1 ≤ width + 3) :
    ArithmeticTop.source width .carry last =
      [Addition.TTK.overflowCarryGate last].map (ArithmeticTop.mapGate width (last + 1) fits) := by
  rw [ArithmeticTop.source, dif_pos (show last < width + 3 by omega), List.map_singleton,
    ArithmeticTop.map_carryGate]

private lemma overflow_stages (last : Nat) :
    Addition.TTK.overflowGates (last + 1) =
      (Addition.TTK.preXorGates (last + 1)).map Addition.TTK.withOverflowGate ++
      (if 0 < last then [Addition.TTK.overflowPreGate last] else []) ++
      (Addition.TTK.descendingXorGates (last + 1)).map Addition.TTK.withOverflowGate ++
      (Addition.TTK.carryGates (last + 1)).map Addition.TTK.withOverflowGate ++
      [Addition.TTK.overflowCarryGate last] ++
      (Addition.TTK.descendingUncomputeGates (last + 1)).map Addition.TTK.withOverflowGate ++
      (Addition.TTK.ascendingXorGates (last + 1)).map Addition.TTK.withOverflowGate ++
      (Addition.TTK.finalXorGates (last + 1)).map Addition.TTK.withOverflowGate := by
  cases last <;> rfl

/-- Every source gate and ordered operand agrees with the complete original signed TTK word. -/
lemma sourceWord_eq_original (width last : Nat) (fits : last + 1 ≤ width + 3) :
    sourceWord width last =
      (Addition.TTK.overflowGates (last + 1)).map
        (ArithmeticTop.mapGate width (last + 1) fits) := by
  simp only [sourceWord, ArithmeticWindow.stages, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, stageWord, ArithmeticSigned.nativeWord, ArithmeticWindow.stageWord,
    List.reverse_append]
  rw [source_pre width last fits, source_carry width last fits]
  simp only [ArithmeticWindow.prefixGates_eq_map_rawPrefix width (last + 1) fits,
    ← List.map_reverse,
    ArithmeticWindow.rawPrefix_preXor, ArithmeticWindow.rawPrefix_descendingXor,
    ArithmeticWindow.rawPrefix_carry, ArithmeticWindow.rawPrefix_descendingUncompute,
    ArithmeticWindow.rawPrefix_ascendingXor, ArithmeticWindow.rawPrefix_finalXor,
    ArithmeticSigned.stage, map_low_word width (last + 1) fits]
  rw [overflow_stages]
  simp only [List.map_append, List.append_assoc]
  split_ifs <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow
