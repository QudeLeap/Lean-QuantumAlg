/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Correctness
import all QuantumAlg.Components.Encoded.BitGates.Word.Complement
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual fixed-constant reflection using the existing two operand words

The first word is real clean workspace. Literal X instructions load the
public constant, complement the second word, and unload the first word
after the original TTK low-word addition. No operand value selects code.
The generic finite-word law is proved before any concrete-width placement.
-/

namespace QuantumAlg.MAU.Addition.TTK.Reflection

noncomputable section

open EncodedBit GateSpec

def leftWord (width : Nat) : EncodedBit.Word (encoding width) width := ⟨leftBit width⟩

def rightWord (width : Nat) : EncodedBit.Word (encoding width) width := ⟨rightBit width⟩

def zero (width : Nat) : Fin (2 ^ width) := ⟨0, Nat.two_pow_pos width⟩

/-- The independent finite-word reflection, including arbitrary binary input values. -/
def reflected {width : Nat} (constant input : Fin (2 ^ width)) : Fin (2 ^ width) :=
  ⟨(constant.val + (2 ^ width - 1 - input.val)) % 2 ^ width,
    Nat.mod_lt _ (Nat.two_pow_pos width)⟩

/-- On canonical residues the same word is the ordinary nonnegative reflected value. -/
lemma reflected_value {width : Nat} (constant input : Fin (2 ^ width))
    (canonical : input.val < constant.val) :
    (reflected constant input).val = constant.val - 1 - input.val := by
  have capacity := Nat.two_pow_pos width
  have inputBound := input.isLt
  have constantBound := constant.isLt
  have expanded : constant.val + (2 ^ width - 1 - input.val) =
      2 ^ width + (constant.val - 1 - input.val) := by omega
  change (constant.val + (2 ^ width - 1 - input.val)) % 2 ^ width = _
  rw [expanded, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

lemma load_zero (width : Nat) (constant input : Fin (2 ^ width)) :
    EncodedBit.Word.xorConstantStep (leftWord width) constant (zero width, input) =
      (constant, input) := by
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have actual := EncodedBit.Word.xorConstantStep_get_target (leftWord width) constant bit
      (fun other different => ttkLeftLeft_disjoint width other bit different) (zero width, input)
    change (leftBit width bit).get
      (EncodedBit.Word.xorConstantStep (leftWord width) constant (zero width, input)) =
        ((leftBit width bit).get (zero width, input) ^^ constant.val.testBit bit.val) at actual
    simpa only [ttkLeftBit_get, zero, Nat.zero_testBit, Bool.false_xor] using actual
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← ttkRightBit_get width bit,
      EncodedBit.Word.xorConstantStep_get_observed_of_target_ne (leftWord width) constant
        (rightBit width bit) (fun other => ttkLeftRight_disjoint width other bit),
      ttkRightBit_get]

lemma unload_known (width : Nat) (constant input : Fin (2 ^ width)) :
    EncodedBit.Word.xorConstantUnloadStep (leftWord width) constant (constant, input) =
      (zero width, input) := by
  have restored := EncodedBit.Word.xorConstantUnloadStep_after_xorConstantStep
    (leftWord width) constant (zero width, input)
  rw [load_zero] at restored
  exact restored

lemma complement_step (width : Nat) (left right : Fin (2 ^ width)) :
    stepList (rightWord width).complementGates (left, right) =
      (left, (~~~BitVec.ofFin right).toFin) := by
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← ttkLeftBit_get width bit,
      EncodedBit.Word.complementGates_get_other (rightWord width) (leftBit width bit)
        (fun other => (ttkLeftRight_disjoint width bit other).symm),
      ttkLeftBit_get]
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have actual := EncodedBit.Word.complementGates_get (rightWord width)
      (fun first second same => by
        by_contra different
        exact ttkRightRight_disjoint width first second different same) (left, right) bit
    change (rightBit width bit).get (stepList (rightWord width).complementGates (left, right)) =
      !(rightBit width bit).get (left, right) at actual
    simp only [ttkRightBit_get] at actual
    apply actual.trans
    change Bool.not (right.val.testBit bit.val) = (~~~BitVec.ofFin right).getLsbD bit.val
    simp only [BitVec.getLsbD_not, bit.isLt, decide_true, Bool.true_and]
    exact congrArg Bool.not (BitVec.getLsbD_ofNatLT right.val right.isLt bit.val).symm

/-- Actual constant load, complete target complement, native addition and own constant unload. -/
def gates (width : Nat) (constant : Fin (2 ^ width)) : List (GateSpec (encoding width)) :=
  EncodedBit.Word.xorConstantGates (leftWord width) constant ++
    ((rightWord width).complementGates ++
      (lowRippleGates width ++
        EncodedBit.Word.xorConstantUnloadGates (leftWord width) constant))

def program (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates width constant)

/-- Exact complete clean-workspace output at every width, without a residue input restriction. -/
lemma gates_clean (width : Nat) (constant input : Fin (2 ^ width)) :
    stepList (gates width constant) (zero width, input) =
      (zero width, reflected constant input) := by
  rw [gates, stepList_append, stepList_append, stepList_append]
  change EncodedBit.Word.xorConstantUnloadStep (leftWord width) constant
    (stepList (lowRippleGates width)
      (stepList (rightWord width).complementGates
        (EncodedBit.Word.xorConstantStep (leftWord width) constant (zero width, input)))) = _
  rw [load_zero, complement_step, ttkLowRipple_step]
  have value : lowOutput (constant, (~~~BitVec.ofFin input).toFin) =
      (constant, reflected constant input) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (constant.val + (~~~BitVec.ofFin input).toNat) % 2 ^ width =
        (constant.val + (2 ^ width - 1 - input.val)) % 2 ^ width
      rw [BitVec.toNat_not, BitVec.toNat_ofFin]
  rw [value]
  exact unload_known width constant _

/-- The emitted word has its full coherent native semantics on every complete input state. -/
lemma program_realizes (width : Nat) (constant : Fin (2 ^ width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width constant) environment
      (stepList (gates width constant)) :=
  realizesList (QubitLayout.canonical _) .empty _ environment

end

end QuantumAlg.MAU.Addition.TTK.Reflection
