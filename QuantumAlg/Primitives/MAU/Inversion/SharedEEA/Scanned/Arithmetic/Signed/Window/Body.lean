/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Source

/-!
# The complete actual streamed signed adder

Six native traversals execute the original TTK stages in their source
order. Every traversal restores the same address, prefix and moving
flag. The selected window is a coherent input; it never selects a
host-generated program [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow

noncomputable section

open EncodedBit ArithmeticTemplate NumberTheory.SharedEEA

/-- The original descending chain and upward carry use the proved actual fused signed streams. -/
def stageProgram (width : Nat) : Stage →
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum
  | .descendingXor => ArithmeticSigned.reverseProgram width .pre
  | .carry => ArithmeticSigned.forwardProgram width .carry
  | stage => ArithmeticWindow.stageProgram width stage

private lemma stageWord_pool (width last : Nat) (stage : Stage) (state : Data width) :
    (GateSpec.stepList (stageWord width last stage) state).2 = state.2 := by
  cases stage with
  | preXor => exact ArithmeticWindow.stageWord_pool width (last + 1) .preXor state
  | descendingXor => exact ArithmeticSigned.nativeWord_reverse_pool width .pre last state
  | carry => exact ArithmeticSigned.nativeWord_pool width .carry last state
  | descendingUncompute =>
      exact ArithmeticWindow.stageWord_pool width (last + 1) .descendingUncompute state
  | ascendingXor => exact ArithmeticWindow.stageWord_pool width (last + 1) .ascendingXor state
  | finalXor => exact ArithmeticWindow.stageWord_pool width (last + 1) .finalXor state

private lemma stageWord_control (width last : Nat) (stage : Stage) (state : Data width) :
    (GateSpec.stepList (stageWord width last stage) state).1.control = state.1.control := by
  cases stage with
  | preXor => exact ArithmeticWindow.stageWord_control width (last + 1) .preXor state
  | descendingXor => exact ArithmeticSigned.nativeWord_reverse_control width .pre last state
  | carry => exact ArithmeticSigned.nativeWord_control width .carry last state
  | descendingUncompute =>
      exact ArithmeticWindow.stageWord_control width (last + 1) .descendingUncompute state
  | ascendingXor => exact ArithmeticWindow.stageWord_control width (last + 1) .ascendingXor state
  | finalXor => exact ArithmeticWindow.stageWord_control width (last + 1) .finalXor state

private lemma stageProgram_apply (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (stageProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (if state.1.control then
          GateSpec.stepList (stageWord width state.2.1.toNat stage) state
          else state))) := by
  cases stage with
  | preXor =>
      exact forwardProgram_apply_nativePrefix width positive .preXor
        environment state clean zero within
  | descendingXor =>
      exact ArithmeticSigned.reverseProgram_apply_nativeWord width positive .pre
        environment state clean zero within
  | carry =>
      exact ArithmeticSigned.forwardProgram_apply_nativeWord width positive .carry
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
          GateSpec.stepList (stagesWord width state.2.1.toNat stages) state
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
          let next := GateSpec.stepList (stageWord width state.2.1.toNat stage) state
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

/-- The fixed original six-stage actual circuit, with both signed overflow boundaries fused. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  stagesProgram width ArithmeticWindow.stages

/-- The same original operand windows and arbitrary Sign implement exact signed addition. -/
lemma program_apply_window (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (if state.1.control then
          ArithmeticTop.windowStep width (state.2.1.toNat + 1) (by omega) state else state))) := by
  have actual := stagesProgram_apply width positive ArithmeticWindow.stages environment
    state clean zero within
  have words : stagesWord width state.2.1.toNat ArithmeticWindow.stages =
      sourceWord width state.2.1.toNat := rfl
  rw [words, sourceWord_eq_original width state.2.1.toNat (by omega)] at actual
  rw [ArithmeticTop.mapped_overflow_step] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow
