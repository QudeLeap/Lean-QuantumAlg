/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.WordArithmetic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.Nat.Binary.Arithmetic

/-!
# Zero-bit and one-bit bases of the HRS recursion

The external interface is the original word and exactly one dirty bit.
For widths at most one, selected X gates implement constant addition and
leave that arbitrary bit untouched. These are only the recursion bases;
the general HRS construction also needs the carry bridge and recursive
half additions [HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open BinaryLabelEncoding
open EncodedBit.GateSpec

/-- The original word and its one external dirty bit. -/
abbrev OneDirtyRegisters (width : Nat) := Fin (2 ^ width) × Bool

/-- Exact word/dirty encoding; the constant is a compile-time parameter. -/
def oneDirtyEncoding (width : Nat) : BinaryLabelEncoding (OneDirtyRegisters width) :=
  prod (finIdentity width) bool

/-- Independent all-input constant-addition contract. -/
def oneDirtyOutput {width : Nat} (constant : Fin (2 ^ width))
    (state : OneDirtyRegisters width) : OneDirtyRegisters width :=
  (addWord constant state.1, state.2)

/-- Word bit in the exact external interface. -/
def oneDirtyWordBit (width : Nat) (bit : Fin width) : EncodedBit (oneDirtyEncoding width) :=
  prodLeftBit (finIdentity width) bool
    (finIdentityBit width (WireAddress.littleEndianWire bit))

/-- The external dirty bit, which is never targeted by the base lists. -/
def oneDirtyBit (width : Nat) : EncodedBit (oneDirtyEncoding width) :=
  prodRightBit (finIdentity width) bool boolBit

lemma hrsOneDirtyWordBit_get (width : Nat) (bit : Fin width)
    (state : OneDirtyRegisters width) :
    (oneDirtyWordBit width bit).get state = state.1.val.testBit bit.val := by
  change state.1.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private lemma wordBits_disjoint (width : Nat) (a b : Fin width) (hne : a ≠ b) :
    (oneDirtyWordBit width a).wire ≠ (oneDirtyWordBit width b).wire := by
  intro h
  have hval := congrArg Fin.val h
  change width - 1 - a.val = width - 1 - b.val at hval
  apply hne
  apply Fin.ext
  omega

private lemma dirty_disjoint (width : Nat) (bit : Fin width) :
    (oneDirtyWordBit width bit).wire ≠ (oneDirtyBit width).wire := by
  intro h
  have hval := congrArg Fin.val h
  change width - 1 - bit.val = width at hval
  omega

private def baseWord (width : Nat) : EncodedBit.Word (oneDirtyEncoding width) width :=
  ⟨oneDirtyWordBit width⟩

/-- Literal X gates selected by the compile-time constant for the recursion bases. -/
def oneDirtyBaseGates (width : Nat) (constant : Fin (2 ^ width)) :
    List (EncodedBit.GateSpec (oneDirtyEncoding width)) :=
  EncodedBit.Word.xorConstantGates (baseWord width) constant

def oneDirtyBaseProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (oneDirtyBaseGates width constant)

/-- At the two base widths, finite xor and finite addition coincide exactly. -/
lemma hrsOneDirtyBase_step (width : Nat) (base : width ≤ 1) (constant : Fin (2 ^ width))
    (state : OneDirtyRegisters width) :
    stepList (oneDirtyBaseGates width constant) state = oneDirtyOutput constant state := by
  change EncodedBit.Word.xorConstantStep (baseWord width) constant state = _
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorConstantStep_get_target
      (baseWord width) constant bit
      (fun other hne => wordBits_disjoint width other bit hne) state
    change (oneDirtyWordBit width bit).get _ =
      ((oneDirtyWordBit width bit).get state ^^ constant.val.testBit bit.val) at hread
    rw [hrsOneDirtyWordBit_get, hrsOneDirtyWordBit_get] at hread
    have hbit : bit.val = 0 := by have := bit.isLt; omega
    have hmod : ((state.1.val + constant.val) % 2 ^ width).testBit bit.val =
        (state.1.val + constant.val).testBit bit.val := by
      rw [Nat.testBit_mod_two_pow]
      simp [bit.isLt]
    have hsum : (state.1.val + constant.val).testBit bit.val =
        (state.1.val.testBit bit.val ^^ constant.val.testBit bit.val) := by
      rw [hbit, Nat.BinaryArithmetic.testBit_add_eq_xor3]
      simp [Nat.BinaryArithmetic.natAddCarry]
    exact hread.trans (hmod.trans hsum).symm
  · exact EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
      (baseWord width) constant (oneDirtyBit width) (dirty_disjoint width) state

/-- The actual base circuit realizes addition with its arbitrary dirty bit restored. -/
lemma hrsOneDirtyBase_realizes (width : Nat) (base : width ≤ 1) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width) (oneDirtyBaseProgram width constant)
      environment
      (oneDirtyOutput constant) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (oneDirtyBaseGates width constant)
    (hrsOneDirtyBase_step width base constant) environment

/-- Exact event and serial-depth counts of the selected base gates. -/
lemma hrsOneDirtyBase_resources (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyBaseProgram width constant).eventCost.card =
        (EncodedBit.Word.constantOneIndices constant).length ∧
      (oneDirtyBaseProgram width constant).evaluatedEventDepth (fun _ => 1) =
        (EncodedBit.Word.constantOneIndices constant).length := by
  change (programList (QubitLayout.canonical _) .empty
      (oneDirtyBaseGates width constant)).eventCost.card = _ ∧
    (programList (QubitLayout.canonical _) .empty
      (oneDirtyBaseGates width constant)).evaluatedEventDepth (fun _ => 1) = _
  rw [programList_eventCost_card, programList_evaluatedEventDepth_unit]
  simp [oneDirtyBaseGates, EncodedBit.Word.xorConstantGates_length]

/-- Base gates occupy at most the original input word, within the exact word/dirty carrier. -/
lemma hrsOneDirtyBase_interface (width : Nat) :
    (oneDirtyEncoding width).width = width + 1 ∧
      (QubitLayout.canonical (oneDirtyEncoding width).width).systemIdx =
        List.range (width + 1) := by
  constructor
  · rfl
  · exact QubitLayout.canonical_systemIdx (width + 1)

end

end QuantumAlg.MAU.Addition.HRS
