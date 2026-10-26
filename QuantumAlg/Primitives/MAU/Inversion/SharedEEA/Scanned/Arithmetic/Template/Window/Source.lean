/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Gates
import all QuantumAlg.Util.List.Threshold

/-!
# Original indexed TTK source words behind the physical stream

The selected length changes only the source theorem's finite operand type.
The actual runtime program remains the same native full-size traversal.
Every sum, chain and carry instruction keeps its source index and its
ordered native operands [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open EncodedBit ArithmeticTemplate

private def rawSum (length : Nat) (index : Fin length) :
    GateSpec (Addition.TTK.encoding length) :=
  .cnot (Addition.TTK.leftBit length index) (Addition.TTK.rightBit length index)
    (Addition.TTK.ttkLeftRight_disjoint length index index)

private def rawChain (length : Nat) (index : Fin length) (positive : 0 < index.val) :
    GateSpec (Addition.TTK.encoding length) :=
  .cnot (Addition.TTK.leftBit length (before length index)) (Addition.TTK.leftBit length index)
    (Addition.TTK.ttkLeftLeft_disjoint length _ _ (before_ne length index positive))

private def rawCarry (length : Nat) (index : Fin length) (positive : 0 < index.val) :
    GateSpec (Addition.TTK.encoding length) :=
  .toffoli (Addition.TTK.rightBit length (before length index))
    (Addition.TTK.leftBit length (before length index)) (Addition.TTK.leftBit length index)
    (Addition.TTK.ttkLeftRight_disjoint length _ _).symm
    (Addition.TTK.ttkLeftRight_disjoint length _ _).symm
    (Addition.TTK.ttkLeftLeft_disjoint length _ _ (before_ne length index positive))

/-- The original six stage masks, on their exact finite TTK operand type. -/
def rawSource (length : Nat) (stage : Stage) (index : Nat) :
    List (GateSpec (Addition.TTK.encoding length)) :=
  if within : index < length then
    let current : Fin length := ⟨index, within⟩
    match stage with
    | .preXor => if 0 < index then [rawSum length current] else []
    | .descendingXor | .ascendingXor =>
        if internal : 2 ≤ index then
          [rawChain length current (by change 0 < index; omega)] else []
    | .carry => if positive : 0 < index then [rawCarry length current positive] else []
    | .descendingUncompute => if positive : 0 < index then
        [rawCarry length current positive, rawSum length current] else []
    | .finalXor => [rawSum length current]
  else []

/-- Every original retained index places exactly the source callback emitted by the real stream. -/
lemma rawSource_map (width length : Nat) (fits : length ≤ width + 3) (stage : Stage)
    (index : Nat) (within : index < length) :
    (rawSource length stage index).map (mapGate width length fits) =
      ArithmeticTemplate.source width stage index := by
  have full : index < width + 3 := lt_of_lt_of_le within fits
  cases stage <;>
    simp only [rawSource, dif_pos within, ArithmeticTemplate.source,
      ArithmeticTemplate.nativeWords, dif_pos full]
  case preXor =>
    split_ifs <;> simp only [List.map_cons, List.map_nil, rawSum, map_sumGate]
  case descendingXor | ascendingXor =>
    split_ifs with internal
    · simpa only [List.map_cons, List.map_nil, rawChain] using
        congrArg (fun gate => [gate])
          (map_chainGate width length fits ⟨index, within⟩ (by change 0 < index; omega))
    · rfl
  case carry =>
    split_ifs with positive
    · simpa only [List.map_cons, List.map_nil, rawCarry] using
        congrArg (fun gate => [gate])
          (map_carryGate width length fits ⟨index, within⟩ positive)
    · rfl
  case descendingUncompute =>
    split_ifs with positive
    · simp only [List.map_cons, List.map_nil, rawCarry, rawSum, map_sumGate]
      exact congrArg (fun gate => [gate, (sumGate width ⟨index, full⟩).val])
        (map_carryGate width length fits ⟨index, within⟩ positive)
    · rfl
  case finalXor =>
    simp only [List.map_cons, List.map_nil, rawSum, map_sumGate]

/-- The complete indexed source word retains its original ascending finite order. -/
def rawPrefix (length : Nat) (stage : Stage) : List (GateSpec (Addition.TTK.encoding length)) :=
  (List.range length).flatMap (rawSource length stage)

private lemma map_flatMap_word {Source Target : Type*} (indices : List Nat)
    (source : Nat → List Source) (placement : Source → Target) :
    (indices.flatMap source).map placement =
      indices.flatMap (fun index => (source index).map placement) := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.map_append, ih]

/-- The actual streamed source prefix is the literal native placement of the original TTK word. -/
lemma prefixGates_eq_map_rawPrefix (width length : Nat) (fits : length ≤ width + 3)
    (stage : Stage) :
    prefixGates width stage length = (rawPrefix length stage).map (mapGate width length fits) := by
  rw [prefixGates, rawPrefix, map_flatMap_word]
  rw [ListThreshold.flatMap_range_eq_flatten_ofFn,
    ListThreshold.flatMap_range_eq_flatten_ofFn]
  apply congrArg List.flatten
  apply congrArg (fun entries : Fin length → List (GateSpec (Scanned.encoding width)) =>
    List.ofFn entries)
  funext index
  exact (rawSource_map width length fits stage index.val index.isLt).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
