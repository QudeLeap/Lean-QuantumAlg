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
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
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

/-- The sole executed circuit realizes the complete independent native event formula. -/
theorem code_events {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).resourcePool path = eventBudget M k := by
  change ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model (Native.oracles M.preparation M.good)
      (runtimeLayout n k) ++ (nativeProgram M k).eventTrace) = _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    nativeProgram, Execution.unitaryOfEqualWires_cost, Native.program_eventCost]
  change ZeroPreparation.eventCost AlgorithmGate.model (Native.oracles M.preparation M.good)
    (runtimeLayout n k) + Native.unitaryEventPool M.preparation M.good k = _
  rw [ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model
    (Native.oracles M.preparation M.good) (runtimeLayout n k) 2 (fun _ => rfl)]
  rfl

/-- The exact depth includes the parallel nonempty zero-preparation layer. -/
theorem code_depth_exact {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) :
    (code M k).depth (fun _ => 1) path =
      (if totalQubits n k = 0 then 0 else 1) + Native.unitaryDepth n k := by
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (Native.oracles M.preparation M.good)
        (runtimeLayout n k)) +
      (Native.program M.preparation M.good k).evaluatedEventDepth (fun _ => 1) = _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
    (Native.oracles M.preparation M.good) (runtimeLayout n k) 2 (fun _ => rfl),
    Native.program_unitDepth]

/-- The independent bound covers every width, including an empty prepared word. -/
theorem code_depth {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) : (code M k).depth (fun _ => 1) path ≤ depthBudget n k := by
  rw [code_depth_exact]
  unfold Native.unitaryDepth depthBudget
  split <;> omega

/-- Known reflections are the sole elementary gates outside the source-query coordinates. -/
theorem code_gateCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (code M k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code M k).resourcePool path) =
        k * ZeroReflection.elementaryGateCount n := by
  let weight : Resource.Event (model M) → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight ((code M k).resourcePool path) = _
  have actual : ResourcePool.weightedCount weight (Native.unitaryEventPool M.preparation M.good k) =
      k * ZeroReflection.elementaryGateCount n := by
    rw [← Native.program_eventCost M.preparation M.good k]
    refine Eq.trans ?_ (Native.program_gateCount M.preparation M.good k)
    apply congrArg (fun assignment : Resource.Event (model M) → Nat =>
      ResourcePool.weightedCount assignment (Native.program M.preparation M.good k).eventCost)
    funext event
    cases event <;> rfl
  rw [code_events]
  simp only [eventBudget, ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton]
  rw [actual]
  dsimp only [weight]
  omega

end

end QuantumAlg.AmplitudeAmplification
