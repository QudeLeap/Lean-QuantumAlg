/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Specification
import all QuantumAlg.Primitives.AmplitudeAmplification.Program.Resources
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import Mathlib.Data.List.OfFn

/-!
# Complete actual amplification resources

The one executed trace includes actual zero preparation and each distinct
source call. Its elementary gates and depth agree with independent formulas,
including the zero-iteration case and every helper-width branch.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

open QuantumAlg.ZeroReflection.Workspace
open QuantumAlg.AmplitudeAmplificationSource

private theorem preparation_value (n k : Nat) (index : Fin (totalQubits n k)) :
    ((inputPreparation n k).value index).val = 0 := by
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ totalQubits n k)).val.testBit index.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

theorem inputPreparation_event (n k : Nat) :
    (inputPreparation n k).event = basisPreparationEvent (totalQubits n k) := by
  have dimensions : (runtimeLayout n k).dimensions.map PNat.val =
      List.replicate (totalQubits n k) 2 := by
    change (List.ofFn (fun _ : Fin (totalQubits n k) => (2 : ℕ+))).map PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const (totalQubits n k) 2
  have values : List.ofFn (fun index => ((inputPreparation n k).value index).val) =
      List.replicate (totalQubits n k) 0 := by
    simp only [preparation_value, List.ofFn_const]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis"
      parameters := totalQubits n k ::
        ((runtimeLayout n k).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation n k).value index).val)) } = _
  rw [dimensions, values]
  rfl

/-- The sole executed circuit realizes the complete independent native event formula. -/
theorem code_events {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).resourcePool path = eventBudget n k := by
  change ResourcePool.ofList
    ([(inputPreparation n k).event] ++ (nativeProgram M k).eventTrace) = _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    add_zero, inputPreparation_event, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    nativeProgram, UnitaryCircuit.reindex_eventCost, Native.program_eventCost]
  rfl

/-- Exact unit-event depth includes the initial basis preparation. -/
theorem code_depth {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).depth (fun _ => 1) path = depthBudget n k := by
  change 1 + (Native.program M.preparation M.good k).evaluatedEventDepth (fun _ => 1) = _
  rw [Native.program_unitDepth]
  unfold Native.unitaryDepth depthBudget
  omega

/-- Known reflections are the sole elementary gates outside the source-query coordinates. -/
theorem code_gateCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code M k).resourcePool path) =
        k * ZeroReflection.elementaryGateCount n := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight ((code M k).resourcePool path) = _
  have actual : ResourcePool.weightedCount weight (Native.unitaryEventPool n k) =
      k * ZeroReflection.elementaryGateCount n := by
    rw [← Native.program_eventCost M.preparation M.good k]
    exact Native.program_gateCount M.preparation M.good k
  rw [code_events]
  simp only [eventBudget, ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton]
  rw [actual]
  dsimp only [weight, basisPreparationEvent]
  omega

end

end QuantumAlg.AmplitudeAmplification
