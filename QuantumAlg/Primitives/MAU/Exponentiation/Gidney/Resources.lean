/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Native resources of the selected-power fold

The independent pool gives each exponent stage one coherently controlled
unit-multiplier budget. Native control coordinates remain distinct, including
controls already present in modular accumulation. Shared controls serialize
the actual native events. The exact serial depth is the actual event count;
the numerical bound is the number of stages times the multiplier envelope.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation

/-- Independent native coordinates of one selected unit-multiplication stage. -/
def stageNativeBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 (Multiplication.Gidney.nativeBudget width)

/-- Independent pool for one stage per exponent bit. -/
def nativeBudget (exponentWidth width : Nat) : ResourcePool .quantum :=
  exponentWidth • stageNativeBudget width

/-- Explicit total-event and unit-duration serial-depth envelope. -/
def eventBound (exponentWidth width : Nat) : Nat :=
  exponentWidth * Multiplication.Gidney.eventBound width

/-- The addressed quantum control transforms the actual body event coordinates exactly. -/
theorem gidneyExponentStage_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).eventCost =
      ResourcePool.controlForDimension 2
        (Multiplication.Gidney.program width modulus (stageUnit base bit)).eventCost := by
  unfold stageProgram UnitaryCircuit.controlAtEncodedBit
  change (UnitaryCircuit.prodRight
    (m := UnitaryCircuit.encodedControlPrefixWidth (exponentBit exponentWidth bit))
    (UnitaryCircuit.controlLeading (UnitaryCircuit.prodRight
      (m := UnitaryCircuit.encodedControlSuffixWidth (exponentBit exponentWidth bit))
      (Multiplication.Gidney.program width modulus (stageUnit base bit))))).eventCost = _
  rw [UnitaryCircuit.prodRight_eventCost, UnitaryCircuit.controlLeading_eventCost,
    UnitaryCircuit.prodRight_eventCost]

theorem gidneyExponentStage_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).eventCost ≤ stageNativeBudget width := by
  rw [gidneyExponentStage_eventCost]
  exact (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr
    (Multiplication.Gidney.gidneyUnitMultiplication_native_bound
      width modulus (stageUnit base bit))

theorem gidneyExponentStage_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).eventCost.card ≤
      Multiplication.Gidney.eventBound width := by
  rw [gidneyExponentStage_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]
  exact Multiplication.Gidney.gidneyUnitMultiplication_event_count_bound
    width modulus (stageUnit base bit)

/-- The actual addressed selector serializes the complete native stage. -/
theorem gidneyExponentStage_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    (stageProgram exponentWidth width modulus base bit).evaluatedEventDepth (fun _ => 1) =
      (stageProgram exponentWidth width modulus base bit).eventCost.card := by
  let body := UnitaryCircuit.prodRight
    (m := UnitaryCircuit.encodedControlSuffixWidth (exponentBit exponentWidth bit))
    (Multiplication.Gidney.program width modulus (stageUnit base bit))
  change (UnitaryCircuit.prodRight
    (m := UnitaryCircuit.encodedControlPrefixWidth (exponentBit exponentWidth bit))
    (UnitaryCircuit.controlLeading body)).evaluatedEventDepth (fun _ => 1) =
      (UnitaryCircuit.prodRight
        (m := UnitaryCircuit.encodedControlPrefixWidth (exponentBit exponentWidth bit))
        (UnitaryCircuit.controlLeading body)).eventCost.card
  rw [UnitaryCircuit.prodRight_evaluatedEventDepth, UnitaryCircuit.prodRight_eventCost,
    UnitaryCircuit.controlLeading_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]
  calc
    _ = DepthExpr.costEval (fun _ => (1 : Nat))
        (UnitaryCircuit.shiftPhysicalIdx 1 body).eventDepth :=
      UnitaryCircuit.evaluatedEventDepth_controlQubitsAt (fun _ => 1) [0]
        (UnitaryCircuit.shiftPhysicalIdx 1 body) (UnitaryCircuit.leadingControlLayout body)
        (1 : Fin 2)
    _ = body.resourcesFromEventDepth.card := by
      rw [UnitaryCircuit.shiftPhysicalIdx_eventDepth]
      exact DepthExpr.unitCost_eq_eventPool_card _
    _ = body.eventCost.card :=
      congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost body)

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
      bits.length * Multiplication.Gidney.eventBound width := by
  induction bits with
  | nil =>
      change 0 ≤ 0 * Multiplication.Gidney.eventBound width
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
  unfold program
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  simpa only [List.length_ofFn, nativeBudget] using
    gidneyExponentBits_native_bound exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- The actual complete event cardinality obeys the independent selected-stage envelope. -/
theorem gidneyExponent_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).eventCost.card ≤
      eventBound exponentWidth width := by
  unfold program
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  simpa only [List.length_ofFn, eventBound] using gidneyExponentBits_event_count_bound
    exponentWidth width modulus base (List.ofFn fun bit => bit)

/-- Every stage's shared-control schedule is retained in the complete circuit depth. -/
theorem gidneyExponent_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) =
      (program exponentWidth width modulus base).eventCost.card := by
  unfold program
  rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]
  change (programForBits exponentWidth width modulus base
    (List.ofFn fun bit => bit)).evaluatedEventDepth (fun _ => 1) + 0 = _
  rw [Nat.add_zero]
  exact gidneyExponentBits_depth_eq_events exponentWidth width modulus base
    (List.ofFn fun bit => bit)

theorem gidneyExponent_depth_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (program exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) ≤
      eventBound exponentWidth width := by
  rw [gidneyExponent_depth_eq_events]
  exact gidneyExponent_event_count_bound exponentWidth width modulus base

/-- The declared carrier has precisely the exponent and the two reused multiplication words. -/
theorem gidneyExponent_qubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (encoding exponentWidth width).width = exponentWidth + 2 * width ∧
      (program exponentWidth width modulus base).physical_idx.length =
        exponentWidth + 2 * width := by
  constructor
  · change exponentWidth + (width + width) = exponentWidth + 2 * width
    omega
  · rw [gidneyExponent_physical, List.length_range]

end

end QuantumAlg.MAU.Exponentiation.Gidney
