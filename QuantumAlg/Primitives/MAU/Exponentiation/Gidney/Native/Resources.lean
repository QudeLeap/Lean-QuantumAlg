/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Program
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Exact resources of literal native modular exponentiation

Every fresh work qubit contributes its actual zero-preparation event. Every
remaining event is read from the emitted X/CNOT/Toffoli program. No arithmetic
macro, relabelled cost, or black-box query is used in this budget.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits
open EncodedBit.GateSpec

/-- Independent X-loader allowance for every default native coordinate. -/
def identityNativeBudget (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  width • primitiveAlphabet

/-- The preparation pool is charged separately from the parameter-only
arithmetic envelope. No implementation ledger appears in this specification. -/
def arithmeticPreparedNativeBudget (exponentWidth width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty
      (workLayout exponentWidth width) +
    (identityNativeBudget width +
      (oracleNativeBudget exponentWidth width + identityNativeBudget width))

/-- Parameter-only duration bound for preparation and the complete arithmetic
compute, copy, uncompute circuit. -/
def arithmeticPreparedNativeDepth (exponentWidth width : Nat) : Nat :=
  (if width + width = 0 then 0 else 1) +
    (8 * exponentWidth * Multiplication.Gidney.eventBound width + 3 * width)

private lemma identityLoad_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityLoadProgram exponentWidth width modulus positive).eventCost ≤
      identityNativeBudget width := by
  apply ResourcePool.le_scaled_of_support_card_le
  · intro focus present
    exact programList_native_support _ _ focus present
  · exact identityLoadProgram_eventCount exponentWidth width modulus positive

private lemma identityUnload_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityUnloadProgram exponentWidth width modulus positive).eventCost ≤
      identityNativeBudget width := by
  apply ResourcePool.le_scaled_of_support_card_le
  · intro focus present
    exact programList_native_support _ _ focus present
  · exact identityUnloadProgram_eventCount exponentWidth width modulus positive

/-- The arithmetic source circuit obeys the parameter-only independent pool. -/
lemma arithmeticNativeSourceProgram_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost ≤
      identityNativeBudget width +
        (oracleNativeBudget exponentWidth width + identityNativeBudget width) := by
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, placedArithmeticOracle_eventCost]
  exact add_le_add (identityLoad_native_bound exponentWidth width modulus positive)
    (add_le_add (gidneyExponentOracle_native_bound exponentWidth width modulus base)
      (identityUnload_native_bound exponentWidth width modulus positive))

private lemma primitiveAlphabet_gate_count (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate) primitiveAlphabet = 1 := by
  cases coordinate <;> simp only [primitiveAlphabet, ResourcePool.count_ofList] <;> decide

private lemma copyNativeBudget_gate_count_le (width : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate) (copyNativeBudget width) ≤ width := by
  calc
    _ ≤ (copyNativeBudget width).card := Multiset.count_le_card _ _
    _ = width := by
      simp only [copyNativeBudget, ResourcePool.ofList, Multiset.coe_card,
        List.length_replicate]

/-- Each of the three independent arithmetic gate coordinates has the
prescribed parameter-only cap, with preparation accounted separately. -/
lemma arithmeticNativeGateBudget_coordinate (exponentWidth width : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate)
      (identityNativeBudget width +
        (oracleNativeBudget exponentWidth width + identityNativeBudget width)) ≤
      8 * exponentWidth * Multiplication.Gidney.eventBound width + 3 * width := by
  simp only [identityNativeBudget, oracleNativeBudget, nativeBudget, stageNativeBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul,
    primitiveAlphabet_gate_count]
  have copy := copyNativeBudget_gate_count_le width coordinate
  unfold stageEventBound
  nlinarith

/-- Actual preparation plus actual arithmetic native events obeys the
independent all-coordinate budget. -/
lemma arithmeticNativeCode_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    (arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path ≤
      arithmeticPreparedNativeBudget exponentWidth width := by
  change ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (workLayout exponentWidth width) ++
      (arithmeticNativeUnitary exponentWidth width modulus positive base).eventTrace) ≤ _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    arithmeticNativeUnitary_eventCost]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (workLayout exponentWidth width) +
        (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost ≤
    ZeroPreparation.eventCost AlgorithmGate.model .empty
      (workLayout exponentWidth width) +
        (identityNativeBudget width +
          (oracleNativeBudget exponentWidth width + identityNativeBudget width))
  exact add_le_add (le_refl _)
    (arithmeticNativeSourceProgram_native_bound exponentWidth width modulus positive base)

/-- Each actual native gate coordinate of the complete prepared arithmetic
execution obeys the same parameter-only envelope. -/
lemma arithmeticNativeCode_gate_count_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (coordinate : AlgorithmGate.Coordinate)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate)
        ((arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path) ≤
      8 * exponentWidth * Multiplication.Gidney.eventBound width + 3 * width := by
  have bounded := (ResourcePool.le_iff_count.mp
    (arithmeticNativeCode_native_bound exponentWidth width modulus positive base path))
      (.gate coordinate)
  have budget : ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate) (arithmeticPreparedNativeBudget exponentWidth width) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate)
        (identityNativeBudget width +
          (oracleNativeBudget exponentWidth width + identityNativeBudget width)) := by
    rw [arithmeticPreparedNativeBudget, ResourcePool.count_add,
      ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty
        (workLayout exponentWidth width) 2 (fun _ => rfl)]
    simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton,
      reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  exact bounded.trans (budget.le.trans
    (arithmeticNativeGateBudget_coordinate exponentWidth width coordinate))

private lemma identityLoad_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityLoadProgram exponentWidth width modulus positive).evaluatedEventDepth (fun _ => 1) =
      (identityLoadProgram exponentWidth width modulus positive).eventCost.card := by
  rw [identityLoadProgram]
  exact (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
    (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive)).trans
      (EncodedBit.GateSpec.programList_eventCost_card
        (nativeQubitLayout exponentWidth width) .empty
        (identityLoadGates exponentWidth width modulus positive)).symm

private lemma identityUnload_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (identityUnloadProgram exponentWidth width modulus positive).evaluatedEventDepth (fun _ => 1) =
      (identityUnloadProgram exponentWidth width modulus positive).eventCost.card := by
  rw [identityUnloadProgram]
  exact (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
    (nativeQubitLayout exponentWidth width) .empty
    (identityLoadGates exponentWidth width modulus positive).reverse).trans
      (EncodedBit.GateSpec.programList_eventCost_card
        (nativeQubitLayout exponentWidth width) .empty
        (identityLoadGates exponentWidth width modulus positive).reverse).symm

/-- The complete arithmetic source schedule takes one unit-duration step per
emitted elementary event. -/
lemma arithmeticNativeSourceProgram_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base).evaluatedEventDepth
      (fun _ => 1) =
    (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost.card := by
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, Multiset.card_add, Multiset.card_add,
    identityLoad_depth_eq_events, identityUnload_depth_eq_events,
    placedArithmeticOracle, UnitaryCircuit.placeAt_evaluatedEventDepth,
    UnitaryCircuit.placeAt_eventCost, gidneyExponentOracle_depth_eq_events]

/-- The actual runtime placement has the same unit-duration schedule and
native event count as the complete source arithmetic circuit. -/
lemma arithmeticNativeUnitary_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    (arithmeticNativeUnitary exponentWidth width modulus positive base).evaluatedEventDepth
      (fun _ => 1) =
    (arithmeticNativeUnitary exponentWidth width modulus positive base).eventCost.card := by
  rw [arithmeticNativeUnitary_eventCost]
  exact (congrArg (DepthExpr.depthEval (fun _ => (1 : Nat)))
    (Execution.unitaryOfEqualWires_depth (nativeSourceLayout exponentWidth width)
      (preparedContext exponentWidth width).quantumLayout
      (nativeSourceLayout_wires exponentWidth width)
      (arithmeticNativeSourceProgram exponentWidth width modulus positive base)
      .empty .empty)).trans
    (arithmeticNativeSourceProgram_depth_eq_events exponentWidth width modulus positive base)

/-- The complete arithmetic candidate meets the independent serial-depth
envelope, including the actual zero-preparation layer. -/
lemma arithmeticNativeCode_depth_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    (arithmeticNativeCode exponentWidth width modulus positive base).depth (fun _ => 1) path ≤
      arithmeticPreparedNativeDepth exponentWidth width := by
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model .empty
        (workLayout exponentWidth width)) +
    (arithmeticNativeUnitary exponentWidth width modulus positive base).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model .empty
      (workLayout exponentWidth width) 2 (fun _ => rfl),
    arithmeticNativeUnitary_depth_eq_events, arithmeticNativeUnitary_eventCost]
  exact Nat.add_le_add_left
    (arithmeticNativeSourceProgram_gateBound exponentWidth width modulus positive base) _

private lemma work_space (exponentWidth width : Nat) :
    SpacePool.ofQuantumLayout (workLayout exponentWidth width) = space (width + width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (workQubitLayout exponentWidth width).toQuantumLayout_dimensionCount dimension

private lemma complete_space (exponentWidth width : Nat) :
    space (width + width) + space (exponentWidth + width) =
      space (exponentWidth + 3 * width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then width + width else 0) +
        (if (2 : ℕ+) = dimension then exponentWidth + width else 0) =
          if (2 : ℕ+) = dimension then exponentWidth + 3 * width else 0
      split_ifs <;> omega

private lemma input_space_le (exponentWidth width : Nat) :
    space (exponentWidth + width) ≤ space (exponentWidth + 3 * width) := by
  intro axis
  cases axis with
  | classicalBits => exact Nat.le_refl 0
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then exponentWidth + width else 0) ≤
        if (2 : ℕ+) = dimension then exponentWidth + 3 * width else 0
      split_ifs <;> omega

lemma gidneyExponentPreparedContext_resident (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).residentSpace = space (exponentWidth + 3 * width) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout, work_space,
    suppliedQubits_resident, complete_space]

lemma gidneyExponentPreparedContext_auxiliary (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).auxiliarySpace = space (2 * width) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout, work_space,
    suppliedQubits_auxiliary]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then width + width else 0) + 0 =
        if (2 : ℕ+) = dimension then 2 * width else 0
      split_ifs <;> omega

/-- The arithmetic candidate occupies exactly the declared complete carrier
after preparing its two work words. -/
lemma arithmeticNativeCode_resident_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    (arithmeticNativeCode exponentWidth width modulus positive base).peakResidentSpace path ≤
      space (exponentWidth + 3 * width) := by
  intro axis
  change Nat.max ((context (exponentWidth + width)).residentSpace axis)
    (Nat.max ((preparedContext exponentWidth width).residentSpace axis)
      (Nat.max ((preparedContext exponentWidth width).residentSpace axis) 0)) ≤ _
  rw [suppliedQubits_resident, gidneyExponentPreparedContext_resident]
  exact Nat.max_le.mpr ⟨input_space_le exponentWidth width axis,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩

/-- Only the two prepared work words are auxiliary to the caller's exponent
and arbitrary XOR target in the arithmetic candidate. -/
lemma arithmeticNativeCode_auxiliary_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    (arithmeticNativeCode exponentWidth width modulus positive base).peakAuxiliarySpace path ≤
      space (2 * width) := by
  intro axis
  change Nat.max ((context (exponentWidth + width)).auxiliarySpace axis)
    (Nat.max ((preparedContext exponentWidth width).auxiliarySpace axis)
      (Nat.max ((preparedContext exponentWidth width).auxiliarySpace axis) 0)) ≤ _
  rw [suppliedQubits_auxiliary, gidneyExponentPreparedContext_auxiliary]
  exact Nat.max_le.mpr ⟨Nat.zero_le _,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩


end

end QuantumAlg.MAU.Exponentiation.Gidney
