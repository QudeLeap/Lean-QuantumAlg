/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime

/-!
# Independent resources of the complete prepared modular-add inverse

One actual fixed preparation precedes the native arithmetic. The complete
space contains the original input, arbitrary target, supplied flag, and
every retained shared-frame auxiliary. The modulus-one identity branch
still pays for preparation and retains the same physical systems.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateResources

noncomputable section

open Execution AccumulateRuntime

/-- Complete supplied and prepared physical space, including the original flag. -/
def width (inputWidth : Nat) : Nat := 3 * inputWidth + 4 * inputWidth.size + 12

/-- All live systems are dimension-two qubits, with no classical cells in this unitary endpoint. -/
def space (inputWidth : Nat) : SpacePool .quantum := OwnedQubits.space (width inputWidth)

/-- One fixed preparation event and the independent complete modular-add native envelope. -/
def events (modulus : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (InputPreparation.preparation modulus).event +
    Accumulate.nativeBudget modulus.size

/-- Independent unit-event depth charges one preparation before both EEA passes and accumulation. -/
def depthBound (inputWidth : Nat) : Nat := 1 + Accumulate.eventBound inputWidth

private theorem prepared_width (inputWidth : Nat) :
    (PayloadPreparation.frameEncoding inputWidth (inputWidth + 1)).width = width inputWidth := by
  change (encoding inputWidth).width + (inputWidth + 1) = _
  rw [encoding_width]
  unfold width
  omega

private theorem extended_pool (modulus : Nat) (nontrivial : 1 < modulus) :
    (extendedProgram modulus nontrivial).eventCost =
      (Accumulate.program modulus nontrivial).eventCost := by
  change (UnitaryCircuit.prodLeft (n := 1)
    (Accumulate.program modulus nontrivial)).eventCost = _
  exact UnitaryCircuit.prodLeft_eventCost _

private theorem native_pool (modulus : Nat) :
    (nativeProgram modulus).eventCost ≤ Accumulate.nativeBudget modulus.size := by
  by_cases nontrivial : 1 < modulus
  · have selected : nativeProgram modulus = extendedProgram modulus nontrivial :=
      dif_pos nontrivial
    have cost := (congrArg UnitaryCircuit.eventCost selected).trans
      (extended_pool modulus nontrivial)
    exact cost.le.trans (Accumulate.accumulateProgram_native_budget modulus nontrivial)
  · simp only [nativeProgram, dif_neg nontrivial, UnitaryCircuit.identity_eventCost]
    exact zero_le

private theorem native_count (modulus : Nat) :
    (nativeProgram modulus).eventCost.card ≤ Accumulate.eventBound modulus.size := by
  by_cases nontrivial : 1 < modulus
  · have selected : nativeProgram modulus = extendedProgram modulus nontrivial :=
      dif_pos nontrivial
    have cost := (congrArg UnitaryCircuit.eventCost selected).trans
      (extended_pool modulus nontrivial)
    exact (congrArg Multiset.card cost).le.trans
      (Accumulate.accumulateProgram_event_count modulus nontrivial)
  · simp only [nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost, Multiset.card_zero]
    exact Nat.zero_le _

/-- The same actual code meets the independent native-coordinate budget on every path. -/
theorem accumulateResources_events (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).resourcePool path ≤ events modulus := by
  have actual := PayloadRuntime.payloadRuntime_code_resourcePool modulus (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus) path
  have bounded := add_le_add_right (native_pool modulus)
    (ResourcePool.singleton (InputPreparation.preparation modulus).event)
  exact actual.le.trans bounded

/-- The resident peak includes every actually supplied and prepared quantum system. -/
theorem accumulateResources_resident (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).peakResidentSpace path ≤ space modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_resident modulus (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus) path
  rw [prepared_width] at actual
  exact actual

/-- The owned auxiliary peak comes from the same actual visited contexts. -/
theorem accumulateResources_auxiliary (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).peakAuxiliarySpace path ≤ space modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_auxiliary modulus (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus) path
  rw [prepared_width] at actual
  exact actual

/-- Actual sequential depth charges preparation before the same complete selected native program. -/
theorem accumulateResources_depth (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).depth (fun _ => 1) path ≤ depthBound modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_depth modulus (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus) (fun _ => 1) path
  have native := (ShiftResources.unitDepth_le_count (nativeProgram modulus)).trans
    (native_count modulus)
  exact actual.le.trans (Nat.add_le_add_left native 1)

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateResources
