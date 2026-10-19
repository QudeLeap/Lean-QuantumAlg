/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled

/-!
# Outer control pushed through both actual reversible multiplication MACs

The forward MAC, selected three-CNOT swap and reversed inverse-coefficient
MAC use the same original two words. This is the clean-work specialization;
its exact total pair equivalence also specifies arbitrary auxiliary labels.
It does not identify that permutation with the different three-MAC dirty-
work bimultiplication [G17, paper.tex:186-211]. The actual BCBC controls are
pushed through both MAC lists [G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}


open Accumulate.Gidney Nat.FixedWidth EncodedBit GateSpec

/-- The forward actual MAC realizes its selected total pair equivalence. -/
private lemma controlledAccumulate_step (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (state : ControlPushdown.OuterRegisters outerWidth width) :
    stepList (ControlPushdown.twoGates outerWidth width address modulus coefficient) state =
      (state.1, if state.1.val.testBit address.val then
        accumulatePairEquiv modulus coefficient width state.2 else state.2) := by
  simpa only [accumulatePairEquiv_apply, prefixOutput] using
    ControlPushdown.twoGates_step outerWidth width address modulus coefficient state

/-- Reversing the real MAC list gives its exact selected inverse. -/
private lemma controlledInverseAccumulate_step (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (state : ControlPushdown.OuterRegisters outerWidth width) :
    stepList (ControlPushdown.twoGates outerWidth width address modulus coefficient).reverse
        state =
      (state.1, if state.1.val.testBit address.val then
        (accumulatePairEquiv modulus coefficient width).symm state.2 else state.2) := by
  have inverse := stepList_reverse_stepList
    (ControlPushdown.twoGates outerWidth width address modulus coefficient)
    (state.1, if state.1.val.testBit address.val then
      (accumulatePairEquiv modulus coefficient width).symm state.2 else state.2)
  rw [controlledAccumulate_step] at inverse
  cases selected : state.1.val.testBit address.val <;>
    simpa only [selected, Bool.false_eq_true, if_false, if_true, Equiv.apply_symm_apply]
      using inverse

/-- The small-width complete multiplier is unchanged; larger widths push both MAC controls. -/
def controlledGates (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    List (GateSpec (ControlPushdown.outerEncoding outerWidth width)) :=
  if _small : width ≤ 2 then
    ControlPushdown.originalControlled outerWidth width address (gates width modulus coefficient)
  else
    (ControlPushdown.twoGates outerWidth width address modulus
        (coefficient : ZMod modulus.val).val ++
      ControlPushdown.originalControlled outerWidth width address (wordSwapGates width)) ++
      (ControlPushdown.twoGates outerWidth width address modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val).reverse

/-- The entire outer word and total joint multiplier permutation have exact phase. -/
lemma gidneyControlledUnitMultiplicationGates_step (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (state : ControlPushdown.OuterRegisters outerWidth width) :
    stepList (controlledGates outerWidth width address modulus coefficient) state =
      (state.1, if state.1.val.testBit address.val then
        unitMultiplicationPairEquiv modulus coefficient state.2 else state.2) := by
  by_cases small : width ≤ 2
  · simp only [controlledGates, dif_pos small, ControlPushdown.originalControlled_step,
      gidneyUnitMultiplicationGates_step]
  · simp only [controlledGates, dif_neg small, stepList_append, controlledAccumulate_step,
      ControlPushdown.originalControlled_step, gidneyWordSwapGates_step,
      controlledInverseAccumulate_step]
    cases state.1.val.testBit address.val <;> rfl

/-- The literal zero-, one-, and two-bit complete instruction path is retained. -/
lemma gidneyControlledUnitMultiplication_small (outerWidth width : Nat)
    (small : width ≤ 2) (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    controlledGates outerWidth width address modulus coefficient =
      ControlPushdown.originalControlled outerWidth width address
        (gates width modulus coefficient) := by
  rw [controlledGates, dif_pos small]

/-- Execute the same full list whose semantic, ledger and time laws are proved here. -/
def controlledProgram (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlPushdown.outerEncoding outerWidth width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty
    (controlledGates outerWidth width address modulus coefficient)

/-- The complete actual multiplier has exact phase on every joint label. -/
lemma gidneyControlledUnitMultiplication_realizes (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (ControlPushdown.outerEncoding outerWidth width)
      (controlledProgram outerWidth width address modulus coefficient) environment
      (fun state => (state.1, if state.1.val.testBit address.val then
        unitMultiplicationPairEquiv modulus coefficient state.2 else state.2)) :=
  realizesList_congrStep _ _ _
    (gidneyControlledUnitMultiplicationGates_step outerWidth width address modulus coefficient)
      environment

/-- The exact full-state law extends to any encoded external reference. -/
lemma gidneyControlledUnitMultiplication_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod (ControlPushdown.outerEncoding outerWidth width) reference)
      (layout := QubitLayout.canonical
        ((ControlPushdown.outerEncoding outerWidth width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width
        (controlledProgram outerWidth width address modulus coefficient)) environment
      (fun state => ((state.1.1, if state.1.1.val.testBit address.val then
        unitMultiplicationPairEquiv modulus coefficient state.1.2 else state.1.2), state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (gidneyControlledUnitMultiplication_realizes outerWidth width address modulus coefficient)

/-- The previous independent multiplier envelope bounds the two optimized MACs and swap. -/
lemma gidneyControlledUnitMultiplication_length_bound (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (controlledGates outerWidth width address modulus coefficient).length ≤
      4 * eventBound width := by
  by_cases small : width ≤ 2
  · rw [controlledGates, dif_pos small]
    exact (ControlPushdown.originalControlled_length outerWidth width address _).trans
      (Nat.mul_le_mul_left 4 (gidneyUnitMultiplicationGates_length_bound width modulus coefficient))
  · have forward := ControlPushdown.twoGates_bound outerWidth width address modulus
      (coefficient : ZMod modulus.val).val
    have inverse := ControlPushdown.twoGates_bound outerWidth width address modulus
      ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
    have swap := ControlPushdown.originalControlled_length outerWidth width address
      (wordSwapGates width)
    rw [gidneyWordSwap_gate_count] at swap
    simp only [controlledGates, dif_neg small, List.length_append, List.length_reverse]
    unfold eventBound
    omega

/-- Every coordinate and serial duration comes from the same literal new program. -/
lemma gidneyControlledUnitMultiplication_eventCost_time (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (controlledProgram outerWidth width address modulus coefficient).eventCost =
        ResourcePool.ofList
          ((controlledGates outerWidth width address modulus coefficient).map (event .empty)) ∧
      (controlledProgram outerWidth width address modulus coefficient).evaluatedEventDepth
          Resource.Event.quantumDuration =
        (controlledGates outerWidth width address modulus coefficient).length :=
  ⟨programList_eventCost _ _ _, ControlPushdown.native_time _⟩

end

end QuantumAlg.MAU.Multiplication.Gidney
