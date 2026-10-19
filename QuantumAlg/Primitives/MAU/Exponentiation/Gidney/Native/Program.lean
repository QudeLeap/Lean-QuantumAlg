/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Placement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle.Resources
import all QuantumAlg.Core.Execution.Circuit

/-!
# Prepare and execute literal native modular exponentiation

The source program is compiled directly from the finite X/CNOT/Toffoli list.
Equal-wire placement transports that same program to the prepared runtime
context without introducing an instruction or changing its resource trace.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- Load the canonical identity power on the internally prepared first work word. -/
def identityLoadProgram (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    UnitaryCircuit AlgorithmGate.model .empty (nativeSourceLayout exponentWidth width) :=
  EncodedBit.GateSpec.programList (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive)

/-- The literal loader realizes the independently defined all-label XOR. -/
lemma identityLoadProgram_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    UnitaryCircuit.Realizes (nativeEncoding exponentWidth width)
      (identityLoadProgram exponentWidth width modulus positive) environment
      (fun state => xorPower state (unitResidueWord modulus positive 1)) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive)
    (identityLoadGates_step exponentWidth width modulus positive)

/-- Reverse the actual identity loader on the same physical word. -/
def identityUnloadProgram (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    UnitaryCircuit AlgorithmGate.model .empty (nativeSourceLayout exponentWidth width) :=
  EncodedBit.GateSpec.programList (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive).reverse

private lemma xorPower_twice {exponentWidth width : Nat}
    (value : Fin (2 ^ width)) (state : NativeRegisters exponentWidth width) :
    xorPower (xorPower state value) value = state := by
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      change (state.1.1.val ^^^ value.val) ^^^ value.val = state.1.1.val
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · rfl
  · rfl

/-- Reverse physical X gates implement the same independent XOR permutation. -/
lemma identityUnloadProgram_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    UnitaryCircuit.Realizes (nativeEncoding exponentWidth width)
      (identityUnloadProgram exponentWidth width modulus positive) environment
      (fun state => xorPower state (unitResidueWord modulus positive 1)) := by
  apply EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive).reverse
  intro state
  have inverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (identityLoadGates exponentWidth width modulus positive)
    (xorPower state (unitResidueWord modulus positive 1))
  rw [identityLoadGates_step, xorPower_twice] at inverse
  exact inverse

/-- The arithmetic candidate executes load, selected-power compute/copy/uncompute,
and unload on the prescribed prepared source carrier. -/
def arithmeticNativeSourceProgram (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (nativeSourceLayout exponentWidth width) :=
  (identityLoadProgram exponentWidth width modulus positive).seq
    ((placedArithmeticOracle exponentWidth width modulus base).seq
      (identityUnloadProgram exponentWidth width modulus positive))

lemma identityLoadProgram_eventCount (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityLoadProgram exponentWidth width modulus positive).eventCost.card ≤ width := by
  simp only [identityLoadProgram, nativeSourceLayout,
    EncodedBit.GateSpec.programList_eventCost_card,
    identityLoadGates, EncodedBit.Word.xorConstantGates_length]
  exact EncodedBit.Word.constantOneIndices_length_le _

lemma identityUnloadProgram_eventCount (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityUnloadProgram exponentWidth width modulus positive).eventCost.card ≤ width := by
  simp only [identityUnloadProgram, nativeSourceLayout,
    EncodedBit.GateSpec.programList_eventCost_card,
    List.length_reverse]
  simpa only [identityLoadProgram, nativeSourceLayout,
    EncodedBit.GateSpec.programList_eventCost_card] using
      identityLoadProgram_eventCount exponentWidth width modulus positive

/-- The actual candidate's total native events obey the independent arithmetic
envelope, including both literal identity-word X lists. -/
lemma arithmeticNativeSourceProgram_eventCount (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost.card ≤
      2 * width + oracleEventBound exponentWidth width := by
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, Multiset.card_add, Multiset.card_add,
    placedArithmeticOracle_eventCost]
  have load := identityLoadProgram_eventCount exponentWidth width modulus positive
  have unload := identityUnloadProgram_eventCount exponentWidth width modulus positive
  have oracle := gidneyExponentOracle_event_count_bound exponentWidth width modulus base
  omega

/-- The plan's prescribed complete native gate envelope: two controlled
multiplier traversals, result copy, and identity-word load/unload. -/
lemma arithmeticNativeSourceProgram_gateBound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost.card ≤
      8 * exponentWidth * Multiplication.Gidney.eventBound width + 3 * width := by
  calc
    _ ≤ 2 * width + oracleEventBound exponentWidth width :=
      arithmeticNativeSourceProgram_eventCount exponentWidth width modulus positive base
    _ = 8 * exponentWidth * Multiplication.Gidney.eventBound width + 3 * width := by
      unfold oracleEventBound eventBound stageEventBound
      ring

/-- Place the arithmetic candidate on the complete prepared runtime carrier. -/
def arithmeticNativeUnitary (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (preparedContext exponentWidth width).quantumLayout :=
  Execution.unitaryOfEqualWires (nativeSourceLayout exponentWidth width)
    (preparedContext exponentWidth width).quantumLayout
    (nativeSourceLayout_wires exponentWidth width)
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base)

lemma arithmeticNativeUnitary_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ((arithmeticNativeUnitary exponentWidth width modulus positive base).matrix environment) =
      UnitaryOperator.reindex (nativePlacementBasisEquiv exponentWidth width)
        ((arithmeticNativeSourceProgram exponentWidth width modulus positive base).matrix
        environment) :=
  Execution.unitaryOfEqualWires_matrix (nativeSourceLayout exponentWidth width)
    (preparedContext exponentWidth width).quantumLayout
    (nativeSourceLayout_wires exponentWidth width) environment
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base)

lemma arithmeticNativeUnitary_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeUnitary exponentWidth width modulus positive base).eventCost =
      (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost :=
  Execution.unitaryOfEqualWires_cost (nativeSourceLayout exponentWidth width)
    (preparedContext exponentWidth width).quantumLayout
    (nativeSourceLayout_wires exponentWidth width)
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base) .empty .empty

/-- Prepare exactly the prescribed two work words and run the arithmetic
candidate, retaining the complete input and prepared carrier. -/
def arithmeticNativeCode (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Execution.SuppliedQubits.context (exponentWidth + width))
      (preparedContext exponentWidth width) :=
  (Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
    (Execution.SuppliedQubits.context (exponentWidth + width))
    workKey (workLayout exponentWidth width)
    (gidneyExponentWork_fresh exponentWidth width)
    (gidneyExponentWork_disjoint exponentWidth width)).seq
      (Circuit.unitary (arithmeticNativeUnitary exponentWidth width modulus positive base))


end

end QuantumAlg.MAU.Exponentiation.Gidney
