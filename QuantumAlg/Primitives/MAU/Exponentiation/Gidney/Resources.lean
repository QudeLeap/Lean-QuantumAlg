/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Native resources of the selected-power fold

Each selected multiplier stage is compiled into literal default-model gates
on the exponent and the two original multiplication words. The borrowed
control emits at most four instructions per multiplier instruction and returns
its borrowed wire. The independent budget covers all three native coordinates.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation
open EncodedBit.GateSpec

/-- Independent numerical envelope for one addressed multiplier stage. -/
def stageEventBound (width : Nat) : Nat :=
  4 * Multiplication.Gidney.eventBound width

/-- Each default-model primitive coordinate has the independent stage cap. -/
def stageNativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  stageEventBound width • primitiveAlphabet

/-- Independent pool for one stage per exponent bit. -/
def nativeBudget (exponentWidth width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  exponentWidth • stageNativeBudget width

/-- Explicit total-event and unit-duration serial-depth envelope. -/
def eventBound (exponentWidth width : Nat) : Nat :=
  exponentWidth * stageEventBound width

/-- The two control branches compile to at most four gates per multiplier gate. -/
theorem gidneyExponentStageGates_length_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bit : Fin exponentWidth) :
    (stageGates exponentWidth width modulus base bit).length ≤ stageEventBound width := by
  have source := Multiplication.Gidney.gidneyUnitMultiplicationGates_length_bound
    width modulus (stageUnit base bit)
  by_cases small : width ≤ 1
  · simp only [stageGates, dif_pos small, List.length_map]
    unfold stageEventBound
    omega
  · simp only [stageGates, dif_neg small]
    have controlled := controlRightList_length_bound
      (BinaryLabelEncoding.finIdentityBit exponentWidth) (bodyBits width)
      (exponentBits_wire exponentWidth) (bodyBits_wire width)
      (by
        have positive := bit.isLt
        change 5 ≤ exponentWidth + (width + width)
        omega)
      (exponentBit exponentWidth bit)
      (Multiplication.Gidney.gates width modulus (stageUnit base bit))
    unfold stageEventBound
    omega

/-- All stage events use the explicit default-model primitive alphabet. -/
theorem gidneyExponentStage_native_support (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bit : Fin exponentWidth) (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (stageProgram exponentWidth width modulus base bit).eventCost) :
    focus ∈ primitiveAlphabet :=
  programList_native_support _ (stageGates exponentWidth width modulus base bit) focus present

theorem gidneyExponentStage_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).eventCost.card ≤
      stageEventBound width := by
  simp only [stageProgram, encoding, programList_eventCost_card]
  exact gidneyExponentStageGates_length_bound exponentWidth width modulus base bit

theorem gidneyExponentStage_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).eventCost ≤ stageNativeBudget width := by
  exact ResourcePool.le_scaled_of_support_card_le _ _ _
    (gidneyExponentStage_native_support exponentWidth width modulus base bit)
    (gidneyExponentStage_event_count_bound exponentWidth width modulus base bit)

/-- The actual selected stage serializes its emitted native gates. -/
theorem gidneyExponentStage_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).evaluatedEventDepth (fun _ => 1) =
      (stageProgram exponentWidth width modulus base bit).eventCost.card := by
  simp only [stageProgram, encoding, programList_evaluatedEventDepth_unit,
    programList_eventCost_card]

theorem gidneyExponentBits_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    (programForBits exponentWidth width modulus base bits).eventCost ≤
      bits.length • stageNativeBudget width := by
  induction bits with
  | nil => exact le_of_eq (zero_nsmul _).symm
  | cons bit bits ih =>
      change ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).eventCost ≤ _
      rw [UnitaryCircuit.seq_eventCost]
      calc
        _ ≤ stageNativeBudget width + bits.length • stageNativeBudget width :=
          add_le_add (gidneyExponentStage_native_bound exponentWidth width modulus base bit) ih
        _ = (bit :: bits).length • stageNativeBudget width := by
          rw [List.length_cons, add_nsmul, one_nsmul]
          exact add_comm _ _

theorem gidneyExponentBits_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    (programForBits exponentWidth width modulus base bits).eventCost.card ≤
      bits.length * stageEventBound width := by
  induction bits with
  | nil =>
      change 0 ≤ 0 * stageEventBound width
      exact Nat.zero_le _
  | cons bit bits ih =>
      change ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).eventCost.card ≤ _
      rw [UnitaryCircuit.seq_eventCost, Multiset.card_add, List.length_cons, Nat.succ_mul]
      have stage := gidneyExponentStage_event_count_bound exponentWidth width modulus base bit
      omega

theorem gidneyExponentBits_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (bits : List (Fin exponentWidth)) :
    (programForBits exponentWidth width modulus base bits).evaluatedEventDepth (fun _ => 1) =
      (programForBits exponentWidth width modulus base bits).eventCost.card := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change ((stageProgram exponentWidth width modulus base bit).seq
        (programForBits exponentWidth width modulus base bits)).evaluatedEventDepth (fun _ => 1) =
          ((stageProgram exponentWidth width modulus base bit).seq
            (programForBits exponentWidth width modulus base bits)).eventCost.card
      rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        gidneyExponentStage_depth_eq_events, ih]

/-- The full circuit satisfies a separate bound at every native controlled coordinate. -/
theorem gidneyExponent_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).eventCost ≤ nativeBudget exponentWidth width := by
  simpa only [program, List.length_ofFn, nativeBudget] using
    gidneyExponentBits_native_bound exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- The actual complete event cardinality obeys the independent selected-stage envelope. -/
theorem gidneyExponent_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).eventCost.card ≤
      eventBound exponentWidth width := by
  simpa only [program, List.length_ofFn, eventBound] using gidneyExponentBits_event_count_bound
    exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- Every stage's shared-control schedule is retained in the complete circuit depth. -/
theorem gidneyExponent_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) =
      (program exponentWidth width modulus base).eventCost.card := by
  exact gidneyExponentBits_depth_eq_events exponentWidth width modulus base
    (List.ofFn fun bit => bit)

theorem gidneyExponent_depth_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) ≤
      eventBound exponentWidth width := by
  rw [gidneyExponent_depth_eq_events]
  exact gidneyExponent_event_count_bound exponentWidth width modulus base

/-- The declared carrier has precisely the exponent and the two reused multiplication words. -/
theorem gidneyExponent_qubit_count (exponentWidth width : Nat) :
    (encoding exponentWidth width).width = exponentWidth + 2 * width ∧
      (QubitLayout.canonical (encoding exponentWidth width).width).systemIdx.length =
        exponentWidth + 2 * width := by
  obtain ⟨widthEq, physical⟩ := gidneyExponent_interface exponentWidth width
  exact ⟨widthEq, by rw [physical, List.length_range]⟩

end

end QuantumAlg.MAU.Exponentiation.Gidney
