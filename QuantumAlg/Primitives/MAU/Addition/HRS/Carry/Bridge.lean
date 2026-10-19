/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry

/-!
# HRS bridge that cancels the unknown dirty control

The six executed blocks are controlled increment, controlled complement,
carry, controlled increment, carry, controlled complement. Both increments
run forward. Conditional inversion removes dependence on the initial dirty
bit [HRS16, paper.tex:224-226,232-245].

This leaf proves the composition of actual gate lists once their component
actions have been established. It does not allocate registers or assume
resources supplied independently of those lists. The recursive construction
must still instantiate the component lists on its concrete shared layout.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec

/-- Finite increment, including the unique empty word. -/
def incrementWord {n : Nat} (word : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨(word.val + 1) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- Complement turns the two forward increments into an exact cancellation. -/
lemma hrsIncrement_complement_increment (n : Nat) (word : Fin (2 ^ n)) :
    incrementWord (complementWord (incrementWord word)) = complementWord word := by
  apply Fin.ext
  have hword := hrsComplementWord_sum n word
  have hnext := hrsComplementWord_sum n (incrementWord word)
  change ((complementWord (incrementWord word)).val + 1) % 2 ^ n =
    (complementWord word).val
  by_cases hlt : word.val + 1 < 2 ^ n
  · have hval : (incrementWord word).val = word.val + 1 := Nat.mod_eq_of_lt hlt
    have hsmall : (complementWord (incrementWord word)).val + 1 < 2 ^ n := by omega
    rw [Nat.mod_eq_of_lt hsmall]
    omega
  · have hwrap : word.val + 1 = 2 ^ n := by have := word.isLt; omega
    have hval : (incrementWord word).val = 0 := by simp [incrementWord, hwrap]
    have hfull : (complementWord (incrementWord word)).val + 1 = 2 ^ n := by omega
    rw [hfull, Nat.mod_self]
    omega

/-- Shared semantic fields: preserved lower data, high target word, and dirty control. -/
abbrev BridgeRegisters (Low : Type) (highWidth : Nat) := (Low × Fin (2 ^ highWidth)) × Bool

/-- Controlled increment after all internally borrowed bits have been restored. -/
def bridgeIncrementStep {Low : Type} {highWidth : Nat}
    (state : BridgeRegisters Low highWidth) : BridgeRegisters Low highWidth :=
  if state.2 then ((state.1.1, incrementWord state.1.2), state.2) else state

/-- Controlled inversion of the high word; the dirty bit is preserved. -/
def bridgeComplementStep {Low : Type} {highWidth : Nat}
    (state : BridgeRegisters Low highWidth) : BridgeRegisters Low highWidth :=
  if state.2 then ((state.1.1, complementWord state.1.2), state.2) else state

/-- Carry changes only the dirty output, restoring all its internal borrowing. -/
def bridgeCarryStep {Low : Type} {highWidth : Nat} (carry : Low → Bool)
    (state : BridgeRegisters Low highWidth) : BridgeRegisters Low highWidth :=
  (state.1, state.2 ^^ carry state.1.1)

/-- Increment the high word by the carry and preserve the lower data and dirty bit. -/
def bridgeOutput {Low : Type} {highWidth : Nat} (carry : Low → Bool)
    (state : BridgeRegisters Low highWidth) : BridgeRegisters Low highWidth :=
  ((state.1.1, if carry state.1.1 then incrementWord state.1.2 else state.1.2), state.2)

/-- The six component actions cancel an arbitrary initial dirty bit exactly. -/
lemma hrsCarryBridge_steps {Low : Type} (highWidth : Nat) (carry : Low → Bool)
    (state : BridgeRegisters Low highWidth) :
    bridgeComplementStep (bridgeCarryStep carry
      (bridgeIncrementStep (bridgeCarryStep carry
        (bridgeComplementStep (bridgeIncrementStep state))))) = bridgeOutput carry state := by
  rcases state with ⟨⟨low, high⟩, dirty⟩
  cases dirty <;> cases hc : carry low <;>
    simp [bridgeIncrementStep, bridgeComplementStep, bridgeCarryStep, bridgeOutput,
      hc, hrsIncrement_complement_increment, hrsComplementWord_involutive]

variable {Low : Type} {highWidth : Nat}
variable {encoding : BinaryLabelEncoding (BridgeRegisters Low highWidth)}

/-- Actual six-block gate composition on a shared encoding. -/
def carryBridgeGates (increment complement carry : List (EncodedBit.GateSpec encoding)) :
    List (EncodedBit.GateSpec encoding) :=
  increment ++ complement ++ carry ++ increment ++ carry ++ complement

/-- Compile the actual six-block list. -/
def carryBridgeProgram (increment complement carry : List (EncodedBit.GateSpec encoding)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty
    (carryBridgeGates increment complement carry)

/-- Component exact actions imply the exact all-input action of their real composition. -/
lemma hrsCarryBridge_step (increment complement carry : List (EncodedBit.GateSpec encoding))
    (predicate : Low → Bool)
    (hincrement : ∀ state, stepList increment state = bridgeIncrementStep state)
    (hcomplement : ∀ state, stepList complement state = bridgeComplementStep state)
    (hcarry : ∀ state, stepList carry state = bridgeCarryStep predicate state)
    (state : BridgeRegisters Low highWidth) :
    stepList (carryBridgeGates increment complement carry) state =
      bridgeOutput predicate state := by
  simp only [carryBridgeGates, stepList_append, hincrement, hcomplement, hcarry]
  exact hrsCarryBridge_steps highWidth predicate state

/-- Exact amplitudes of the six actual component lists retain all joint coherence. -/
lemma hrsCarryBridge_realizes (increment complement carry : List (EncodedBit.GateSpec encoding))
    (predicate : Low → Bool)
    (hincrement : ∀ state, stepList increment state = bridgeIncrementStep state)
    (hcomplement : ∀ state, stepList complement state = bridgeComplementStep state)
    (hcarry : ∀ state, stepList carry state = bridgeCarryStep predicate state) :
    UnitaryCircuit.Realizes encoding (carryBridgeProgram increment complement carry) environment
      (bridgeOutput predicate) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (carryBridgeGates increment complement carry)
    (hrsCarryBridge_step increment complement carry predicate hincrement hcomplement hcarry)
      environment

/-- The semantic result restores the entire lower component and the dirty bit. -/
lemma hrsCarryBridge_restores (predicate : Low → Bool)
    (state : BridgeRegisters Low highWidth) :
    (bridgeOutput predicate state).1.1 = state.1.1 ∧
      (bridgeOutput predicate state).2 = state.2 := ⟨rfl, rfl⟩

/-- Native coordinates count each actual component list twice. -/
lemma hrsCarryBridge_native_count
    (increment complement carry : List (EncodedBit.GateSpec encoding))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (carryBridgeProgram increment complement carry).eventCost =
      2 * (ResourcePool.count focus
          (programList (QubitLayout.canonical _) .empty increment).eventCost +
        ResourcePool.count focus
          (programList (QubitLayout.canonical _) .empty complement).eventCost +
        ResourcePool.count focus
          (programList (QubitLayout.canonical _) .empty carry).eventCost) := by
  simp only [carryBridgeProgram, carryBridgeGates,
    programList_event_count_eq_sum_eventMultiplicity, List.map_append, List.sum_append]
  omega

/-- Total events come from the six executed lists, with no separate resource witness. -/
lemma hrsCarryBridge_event_count
    (increment complement carry : List (EncodedBit.GateSpec encoding)) :
    (carryBridgeProgram increment complement carry).eventCost.card =
      2 * (increment.length + complement.length + carry.length) := by
  rw [carryBridgeProgram, programList_eventCost_card]
  simp only [carryBridgeGates, List.length_append]
  omega

/-- Unit-duration depth of the actual serial bridge. -/
lemma hrsCarryBridge_serial_depth
    (increment complement carry : List (EncodedBit.GateSpec encoding)) :
    (carryBridgeProgram increment complement carry).evaluatedEventDepth (fun _ => 1) =
      2 * (increment.length + complement.length + carry.length) := by
  rw [carryBridgeProgram, programList_evaluatedEventDepth_unit]
  simp only [carryBridgeGates, List.length_append]
  omega

end

end QuantumAlg.MAU.Addition.HRS
