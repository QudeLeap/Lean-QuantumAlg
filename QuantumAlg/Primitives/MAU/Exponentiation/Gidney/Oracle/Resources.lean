/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Actual resources of reversible modular exponentiation

The independent oracle pool contains two selected-power budgets and the
literal width-CNOT copy pool. Adjoint execution preserves the original
native coordinates. Both computations reuse the same two work words;
the complete physical carrier has exponentWidth plus three times width
qubits, including the arbitrary XOR target.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

/-- Independent exact native CNOT budget for the literal result copy. -/
def copyNativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (List.replicate width
    (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)))

/-- Independent native coordinate budget for compute, copy, and uncompute. -/
def oracleNativeBudget (exponentWidth width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  nativeBudget exponentWidth width +
    (copyNativeBudget width + nativeBudget exponentWidth width)

/-- Explicit total-event and unit-duration serial-depth bound. -/
def oracleEventBound (exponentWidth width : Nat) : Nat :=
  2 * eventBound exponentWidth width + width

private theorem forward_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (forwardProgram exponentWidth width modulus base).eventCost =
      (program exponentWidth width modulus base).eventCost :=
  rfl

private theorem forward_depth (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (forwardProgram exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) =
      (program exponentWidth width modulus base).eventCost.card :=
  (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth width
    (fun _ => 1) (program exponentWidth width modulus base)).trans
      (gidneyExponent_depth_eq_events exponentWidth width modulus base)

private theorem emptyOraclePool (pool : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    AlgorithmGate.oracleFreePool .empty pool = pool := by
  change Multiset.map (AlgorithmGate.oracleFreeEvent .empty) pool = pool
  have identical : AlgorithmGate.oracleFreeEvent .empty = id := by
    funext event
    cases event with
    | classicalOperation coordinate => cases coordinate
    | classicalQuery coordinate => cases coordinate
    | gate _ => rfl
    | oracle coordinate => cases coordinate
    | preparation _ => rfl
    | measurement _ => rfl
  rw [identical, Multiset.map_id]

/-- Exact oracle ledger retains every forward, copy, and adjoint event coordinate. -/
theorem gidneyExponentOracle_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).eventCost =
      (program exponentWidth width modulus base).eventCost +
        (copyNativeBudget width + (program exponentWidth width modulus base).eventCost) := by
  simp only [oracleProgram, oracleBody, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    emptyOraclePool, forward_eventCost, gidneyExponentCopy_eventCost, copyNativeBudget]

/-- Every actual native coordinate obeys its independently specified oracle budget. -/
theorem gidneyExponentOracle_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).eventCost ≤
      oracleNativeBudget exponentWidth width := by
  rw [gidneyExponentOracle_eventCost]
  exact add_le_add (gidneyExponent_native_bound exponentWidth width modulus base)
    (add_le_add (le_refl (copyNativeBudget width))
      (gidneyExponent_native_bound exponentWidth width modulus base))

theorem gidneyExponentOracle_event_count_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).eventCost.card ≤
      oracleEventBound exponentWidth width := by
  rw [gidneyExponentOracle_eventCost, Multiset.card_add, Multiset.card_add]
  have copied : (copyNativeBudget width).card = width := by
    simp only [copyNativeBudget, ResourcePool.ofList, Multiset.coe_card, List.length_replicate]
  rw [copied]
  have computed := gidneyExponent_event_count_bound exponentWidth width modulus base
  unfold oracleEventBound
  omega

/-- The exact forward/copy/adjoint schedule has one unit-duration step per actual native event. -/
theorem gidneyExponentOracle_depth_eq_events (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) =
      (oracleProgram exponentWidth width modulus base).eventCost.card := by
  rw [gidneyExponentOracle_eventCost, Multiset.card_add, Multiset.card_add]
  have copied : (copyNativeBudget width).card = width := by
    simp only [copyNativeBudget, ResourcePool.ofList, Multiset.coe_card, List.length_replicate]
  rw [copied]
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    ((forwardProgram exponentWidth width modulus base).seq
      ((copyProgram exponentWidth width).seq
        ((forwardProgram exponentWidth width modulus base).dagger
          (AlgorithmGate.oracleFreeAdjoints .empty)))) = _
  simp only [UnitaryCircuit.evaluatedEventDepth_seq,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth, forward_depth,
    (gidneyExponentCopy_serial_resources exponentWidth width).2]

theorem gidneyExponentOracle_depth_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (oracleProgram exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) ≤
      oracleEventBound exponentWidth width := by
  rw [gidneyExponentOracle_depth_eq_events]
  exact gidneyExponentOracle_event_count_bound exponentWidth width modulus base

/-- The oracle's declared physical carrier has no quantum storage beyond its four named words. -/
theorem gidneyExponentOracle_qubit_count (exponentWidth width : Nat) :
    (oracleEncoding exponentWidth width).width = exponentWidth + 3 * width ∧
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).systemIdx.length =
        exponentWidth + 3 * width := by
  obtain ⟨size, physical⟩ := gidneyExponentCopy_interface exponentWidth width
  exact ⟨size, by rw [physical, List.length_range]⟩

end

end QuantumAlg.MAU.Exponentiation.Gidney
