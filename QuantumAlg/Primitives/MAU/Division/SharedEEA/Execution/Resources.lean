/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Runtime
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Independent resources of the complete prepared modular-add division

One actual fixed preparation precedes the native arithmetic. The complete
space contains the original input, numerator, target, supplied flag, and
every retained shared-frame auxiliary. The modulus-one identity branch
still pays for preparation and retains the same physical systems.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionResources

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA ExecutionRuntime

/-- Complete supplied and prepared physical space, including the original flag. -/
def width (inputWidth : Nat) : Nat := 4 * inputWidth + 4 * inputWidth.size + 12

/-- All live systems are dimension-two qubits, with no classical cells in this unitary endpoint. -/
def space (inputWidth : Nat) : SpacePool .quantum := OwnedQubits.space (width inputWidth)

/-- Independently count the fixed seed's literal X gates. -/
def seedEvents (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  EncodedBit.Word.BasisLoad.xCount (InputPreparation.loadConstant modulus) •
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit)

/-- Zero allocation, fixed seed loading and the independent native arithmetic envelope. -/
def events (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
    seedEvents modulus + QuantumAlg.MAU.Division.SharedEEA.nativeBudget modulus.size

/-- Independent unit-event depth charges zero allocation, X loading and both EEA passes. -/
def depthBound (inputWidth : Nat) : Nat :=
  1 + InputPreparation.auxiliaryWidth inputWidth +
    QuantumAlg.MAU.Division.SharedEEA.eventBound inputWidth

private theorem prepared_width (inputWidth : Nat) :
    (PayloadPreparation.frameEncoding inputWidth (payloadWidth inputWidth)).width =
      width inputWidth := by
  change (encoding inputWidth).width + payloadWidth inputWidth = _
  rw [encoding_width]
  unfold width payloadWidth
  omega

private theorem extended_pool (modulus : Nat) (nontrivial : 1 < modulus) :
    (nontrivialProgram modulus nontrivial).eventCost =
      (QuantumAlg.MAU.Division.SharedEEA.program modulus nontrivial).eventCost :=
  (UnitaryCircuit.castCanonicalQubitWidth_eventCost
    (divisionPayload_width modulus.size)
    (flagProgram modulus nontrivial)).trans
      (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost _ _)

private theorem load_pool (modulus : Nat) :
    (PayloadPreparation.loadProgram modulus (payloadWidth modulus.size)).eventCost =
      seedEvents modulus := by
  have placed := Execution.PreparationLoaded.program_eventCost
    (PayloadPreparation.before modulus.size (payloadWidth modulus.size))
    PayloadPreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (PayloadPreparation.payloadPreparation_auxiliary_fresh modulus.size (payloadWidth modulus.size))
    (PayloadPreparation.payloadPreparation_auxiliary_disjoint modulus.size
      (payloadWidth modulus.size))
    (EncodedBit.Word.BasisLoad.program (InputPreparation.auxiliaryQubitLayout modulus.size)
      .empty (InputPreparation.loadConstant modulus))
  exact placed.trans (EncodedBit.Word.BasisLoad.basisLoad_eventCost
    (InputPreparation.auxiliaryQubitLayout modulus.size) .empty
    (InputPreparation.loadConstant modulus))

private theorem native_pool (modulus : Nat) :
    (nativeProgram modulus).eventCost ≤
      QuantumAlg.MAU.Division.SharedEEA.nativeBudget modulus.size := by
  by_cases nontrivial : 1 < modulus
  · have selected : nativeProgram modulus = nontrivialProgram modulus nontrivial :=
      dif_pos nontrivial
    have cost := (congrArg UnitaryCircuit.eventCost selected).trans
      (extended_pool modulus nontrivial)
    exact cost.le.trans (divisionProgram_native_budget modulus nontrivial)
  · simp only [nativeProgram, dif_neg nontrivial, UnitaryCircuit.identity_eventCost]
    exact zero_le

private theorem native_count (modulus : Nat) :
    (nativeProgram modulus).eventCost.card ≤
      QuantumAlg.MAU.Division.SharedEEA.eventBound modulus.size := by
  by_cases nontrivial : 1 < modulus
  · have selected : nativeProgram modulus = nontrivialProgram modulus nontrivial :=
      dif_pos nontrivial
    have cost := (congrArg UnitaryCircuit.eventCost selected).trans
      (extended_pool modulus nontrivial)
    exact (congrArg Multiset.card cost).le.trans
      (divisionProgram_event_count modulus nontrivial)
  · simp only [nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost, Multiset.card_zero]
    exact Nat.zero_le _

private theorem add_bound {left right : ResourcePool (.quantum AlgorithmGate.model .empty)}
    (head : ResourcePool (.quantum AlgorithmGate.model .empty))
    (bounded : left ≤ right) : head + left ≤ head + right :=
  add_le_add_right bounded head

/-- The same actual code meets the independent native-coordinate budget on every path. -/
theorem divisionResources_events (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).resourcePool path ≤ events modulus := by
  have actual : (code modulus).resourcePool path =
      ZeroPreparation.eventCost AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) +
      (PayloadPreparation.loadProgram modulus (payloadWidth modulus.size)).eventCost +
        (nativeProgram modulus).eventCost :=
    PayloadRuntime.payloadRuntime_code_resourcePool modulus (payloadWidth modulus.size)
      (nativeProgram modulus) path
  rw [actual, load_pool]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus +
        (nativeProgram modulus).eventCost ≤
    ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus +
        QuantumAlg.MAU.Division.SharedEEA.nativeBudget modulus.size
  exact add_bound
    (ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus)
    (native_pool modulus)

/-- The resident peak includes every actually supplied and prepared quantum system. -/
theorem divisionResources_resident (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).peakResidentSpace path ≤ space modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_resident modulus (payloadWidth modulus.size)
    (nativeProgram modulus) path
  rw [prepared_width] at actual
  exact actual

/-- The owned auxiliary peak comes from the same actual visited contexts. -/
theorem divisionResources_auxiliary (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).peakAuxiliarySpace path ≤ space modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_auxiliary modulus (payloadWidth modulus.size)
    (nativeProgram modulus) path
  rw [prepared_width] at actual
  exact actual

/-- Actual sequential depth charges preparation before the same complete selected native program. -/
theorem divisionResources_depth (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).depth (fun _ => 1) path ≤ depthBound modulus.size := by
  have actual : (code modulus).depth (fun _ => 1) path =
      DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model .empty
          (InputPreparation.auxiliaryLayout modulus.size)) +
      (PayloadPreparation.loadProgram modulus (payloadWidth modulus.size)).evaluatedEventDepth
        (fun _ => 1) +
      (nativeProgram modulus).evaluatedEventDepth (fun _ => 1) :=
    PayloadRuntime.payloadRuntime_code_depth modulus (payloadWidth modulus.size)
      (nativeProgram modulus) (fun _ => 1) path
  have native := (ShiftResources.unitDepth_le_count (nativeProgram modulus)).trans
    (native_count modulus)
  have zeroBound :
      (if InputPreparation.auxiliaryWidth modulus.size = 0 then 0 else 1) ≤ 1 := by
    split_ifs <;> omega
  have loadBound := (PayloadPreparation.loadProgram_resources modulus (payloadWidth modulus.size)).2
  rw [actual, ZeroPreparation.zeroPreparation_unit_depth]
  unfold depthBound
  omega

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionResources
