/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Complement

/-!
# Literal target-word complement for the bi-flip

The bi-flip subtracts its pivot and then complements the target word
[G17, paper.tex:276-277]. This module provides the latter block as exactly
one addressed X per target bit, including the empty word. It has no helper
register. The finite complement and its bitwise identity are shared with
the HRS arithmetic component.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open BinaryLabelEncoding
open EncodedBit.GateSpec

private def complementBit (width : Nat) (bit : Fin width) :
    EncodedBit (finIdentity width) :=
  finIdentityBit width (WireAddress.littleEndianWire bit)

private def complementWord (width : Nat) : EncodedBit.Word (finIdentity width) width :=
  ⟨complementBit width⟩

private def allOnes (width : Nat) : Fin (2 ^ width) :=
  ⟨2 ^ width - 1, by have := Nat.two_pow_pos width; omega⟩

private theorem complementBit_get (width : Nat) (bit : Fin width)
    (input : Fin (2 ^ width)) :
    (complementBit width bit).get input = input.val.testBit bit.val := by
  change input.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem complementBit_disjoint (width : Nat) (left right : Fin width)
    (hne : left ≠ right) :
    (complementBit width left).wire ≠ (complementBit width right).wire := by
  intro h
  have hv := congrArg Fin.val h
  change width - 1 - left.val = width - 1 - right.val at hv
  apply hne
  apply Fin.ext
  omega

private theorem allOnes_testBit (width : Nat) (bit : Fin width) :
    (allOnes width).val.testBit bit.val = true := by
  simp [allOnes, bit.isLt]

/-- The literal target-only X schedule, in increasing little-endian bit order. -/
def complementGates (width : Nat) : List (EncodedBit.GateSpec (finIdentity width)) :=
  List.ofFn fun bit : Fin width => .x (complementBit width bit)

/-- Compile the real X schedule without an auxiliary register. -/
def complementProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical width).toQuantum :=
  programList (QubitLayout.canonical width) .empty (complementGates width)

private theorem complementGates_eq_xorConstant (width : Nat) :
    complementGates width =
      EncodedBit.Word.xorConstantGates (complementWord width) (allOnes width) := by
  have hbits : (fun bit : Fin width => (allOnes width).val.testBit bit.val) =
      fun _ => true := by
    funext bit
    exact allOnes_testBit width bit
  simp only [EncodedBit.Word.xorConstantGates, EncodedBit.Word.constantOneIndices, hbits]
  simp [complementGates, complementWord, Function.comp_def]

theorem gidneyComplement_step (width : Nat) (input : Fin (2 ^ width)) :
    stepList (complementGates width) input = HRS.complementWord input := by
  rw [complementGates_eq_xorConstant]
  change EncodedBit.Word.xorConstantStep (complementWord width) (allOnes width) input = _
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  have h := EncodedBit.Word.xorConstantStep_get_target
    (complementWord width) (allOnes width) bit
    (fun other hne => complementBit_disjoint width other bit hne) input
  change (complementBit width bit).get _ =
    ((complementBit width bit).get input ^^ (allOnes width).val.testBit bit.val) at h
  rw [complementBit_get, complementBit_get, allOnes_testBit] at h
  simpa only [HRS.hrsComplementWord_testBit, Bool.xor_true] using h

theorem gidneyComplement_realizes (width : Nat) :
    UnitaryCircuit.Realizes (finIdentity width) (complementProgram width) HRS.complementWord := by
  unfold complementProgram
  exact realizesList_congrStep (QubitLayout.canonical width) .empty
    (complementGates width) (gidneyComplement_step width)

/-- Every event is an actual X, one for each target bit. -/
theorem gidneyComplement_eventCost (width : Nat) :
    (complementProgram width).eventCost = ResourcePool.ofList
      (List.replicate width
        (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .singleQubit)) := by
  rw [complementProgram, programList_eventCost]
  congr 1
  have nativeX (bit : Fin width) :
      event .empty (.x (complementBit width bit)) =
        (.gate .singleQubit :
          Resource.Event (.quantum AlgorithmGate.model .empty)) := rfl
  rw [complementGates, List.map_ofFn]
  change List.ofFn (event .empty ∘ fun bit => .x (complementBit width bit)) = _
  rw [show (event .empty ∘ fun bit => .x (complementBit width bit)) =
      (fun _ : Fin width =>
        (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model .empty))) by
    funext bit
    exact nativeX bit]
  exact List.ofFn_const width _

theorem gidneyComplement_depth (width : Nat) :
    (complementProgram width).evaluatedEventDepth (fun _ => 1) = width := by
  rw [complementProgram, programList_evaluatedEventDepth_unit]
  simp [complementGates]

end

end QuantumAlg.MAU.Addition.Gidney
