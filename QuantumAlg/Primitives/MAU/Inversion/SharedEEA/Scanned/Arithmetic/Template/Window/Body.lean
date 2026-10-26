/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Stages
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Reverse

/-!
# The complete actual streamed low-word adder

Six native traversals execute the original TTK stages in their source
order. Every traversal restores the same address, prefix and moving
flag. The selected window is a coherent input; it never selects a
host-generated program [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open EncodedBit ArithmeticTemplate NumberTheory.SharedEEA

/-- Only the two descending stages use an actual native unitary inverse. -/
def stageProgram (width : Nat) : Stage →
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum
  | .descendingXor => reverseProgram width .descendingXor
  | .descendingUncompute => reverseProgram width .descendingUncompute
  | stage => forwardProgram width stage

/-- The literal source word corresponding to the actual stage orientation. -/
def stageWord (width count : Nat) : Stage → List (GateSpec (Scanned.encoding width))
  | .descendingXor => (prefixGates width .descendingXor count).reverse
  | .descendingUncompute => (prefixGates width .descendingUncompute count).reverse
  | stage => prefixGates width stage count

private lemma stageWord_pool (width count : Nat) (stage : Stage) (state : Data width) :
    (GateSpec.stepList (stageWord width count stage) state).2 = state.2 := by
  cases stage <;> first
    | exact prefixGates_pool width _ count state
    | exact prefixGates_reverse_pool width _ count state

private lemma stageWord_control (width count : Nat) (stage : Stage) (state : Data width) :
    (GateSpec.stepList (stageWord width count stage) state).1.control = state.1.control := by
  cases stage <;> first
    | exact prefixGates_control width _ count state
    | exact prefixGates_reverse_control width _ count state

private lemma stageProgram_apply (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (stageProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (if state.1.control then
          GateSpec.stepList (stageWord width (state.2.1.toNat + 1) stage) state
          else state))) := by
  cases stage with
  | preXor =>
      exact forwardProgram_apply_nativePrefix width positive .preXor
        environment state clean zero within
  | descendingXor =>
      exact reverseProgram_apply_nativePrefix width positive .descendingXor
        environment state clean zero within
  | carry =>
      exact forwardProgram_apply_nativePrefix width positive .carry
        environment state clean zero within
  | descendingUncompute =>
      exact reverseProgram_apply_nativePrefix width positive .descendingUncompute
        environment state clean zero within
  | ascendingXor =>
      exact forwardProgram_apply_nativePrefix width positive .ascendingXor
        environment state clean zero within
  | finalXor =>
      exact forwardProgram_apply_nativePrefix width positive .finalXor
        environment state clean zero within

/-- The actual sequence is fixed entirely by public width and the static source stages. -/
def stagesProgram (width : Nat) : List Stage →
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical _).toQuantum
  | stage :: rest => .seq (stageProgram width stage) (stagesProgram width rest)

/-- The original native words remain in their complete chronological stage order. -/
def stagesWord (width count : Nat) (stages : List Stage) :
    List (GateSpec (Scanned.encoding width)) :=
  stages.flatMap (stageWord width count)

private lemma stagesProgram_apply (width : Nat) (positive : 1 ≤ width) (stages : List Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (stagesProgram width stages).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (if state.1.control then
          GateSpec.stepList (stagesWord width (state.2.1.toNat + 1) stages) state
          else state))) := by
  induction stages generalizing state with
  | nil =>
      simp only [stagesWord, List.flatMap_nil, GateSpec.stepList, id_eq, ite_self]
      exact (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (Scanned.encoding width) (QubitLayout.canonical _) environment).apply_encoded_ket state
  | cons stage rest ih =>
      rw [stagesProgram, UnitaryCircuit.applyNormalized_seq,
        stageProgram_apply width positive stage environment state clean zero within]
      cases enabled : state.1.control with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [ih state clean zero within]
          simp only [enabled, Bool.false_eq_true, if_false]
      | true =>
          simp only [if_true]
          let next := GateSpec.stepList (stageWord width (state.2.1.toNat + 1) stage) state
          have pool : next.2 = state.2 := stageWord_pool width _ stage state
          have address : next.2.1 = state.2.1 := congrArg Prod.fst pool
          have nextClean : next.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
            (congrArg (fun value : Pool width => value.2.1) pool).trans clean
          have nextZero : next.2.2.2 = false :=
            (congrArg (fun value : Pool width => value.2.2) pool).trans zero
          have nextWithin : next.2.1.toNat < width + 3 := by rw [address]; exact within
          have nextControl : next.1.control = true :=
            (stageWord_control width _ stage state).trans enabled
          have tail := ih next nextClean nextZero nextWithin
          rw [nextControl, if_pos rfl, address] at tail
          simpa only [stagesWord, List.flatMap_cons, GateSpec.stepList_append] using tail

/-- The original six TTK stages, including the exact two descending words. -/
def stages : List Stage :=
  [.preXor, .descendingXor, .carry, .descendingUncompute, .ascendingXor, .finalXor]

/-- The real six-traversal native circuit on the existing source and pool wires. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  stagesProgram width stages

/-- Placing the original six source words is exactly the source list executed by the full stream. -/
lemma stagesWord_eq_original (width length : Nat) (fits : length ≤ width + 3) :
    stagesWord width length stages =
      (Addition.TTK.lowRippleGates length).map (mapGate width length fits) := by
  simp only [stagesWord, stages, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    stageWord, prefixGates_eq_map_rawPrefix width length fits, ← List.map_reverse,
    rawPrefix_preXor, rawPrefix_descendingXor, rawPrefix_carry,
    rawPrefix_descendingUncompute, rawPrefix_ascendingXor, rawPrefix_finalXor]
  simp only [Addition.TTK.lowRippleGates, List.map_append, List.append_assoc]

/-- Exact full-frame arithmetic retains the complete physical complement and the restored pool. -/
lemma program_apply_window (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (if state.1.control then
          (placement width (state.2.1.toNat + 1) (by omega)).step state else state))) := by
  have actual := stagesProgram_apply width positive stages environment state clean zero within
  rw [stagesWord_eq_original width (state.2.1.toNat + 1) (by omega)] at actual
  have native := (placement width (state.2.1.toNat + 1) (by omega)).subsystem.placeGates_step
    (source_onto _) (Scanned.encoding_surjective width)
    (Addition.TTK.lowRippleGates (state.2.1.toNat + 1)) state
  simp only [Addition.TTK.ttkLowRipple_step] at native
  change GateSpec.stepList
      ((Addition.TTK.lowRippleGates (state.2.1.toNat + 1)).map
        (mapGate width (state.2.1.toNat + 1) (by omega))) state =
      (placement width (state.2.1.toNat + 1) (by omega)).step state at native
  rw [native] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
