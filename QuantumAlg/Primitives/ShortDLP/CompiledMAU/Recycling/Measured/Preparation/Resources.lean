/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Reload
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Actual preparation and native loading resources for the sole measured frame

Every one of the 2n+4 systems has a real preparation event. All retained
output and vent cells are allocated once. The actual literal X word then
loads the same complete seed, without a supplied clean input or a second
quantum bank [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

/-- Independent native pool of the complete initial preparation and literal seed loading. -/
def measuredPreparationBudget (width N : Nat) : ResourcePool model :=
  (2 * width + 4) • ResourcePool.singleton (model := model) (.preparation (2 : ℕ+)) +
    EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
      ResourcePool.singleton (model := model) (.gate .singleQubit)

private lemma measuredPreparation_bank_events (width : Nat) :
    ZeroPreparation.eventCost AlgorithmGate.model .empty (Physical.qubits width).toQuantum
        BitWord.model .empty =
      (2 * width + 4) • ResourcePool.singleton (model := model) (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty
    (Physical.qubits width).toQuantum 2 (fun _ => rfl) BitWord.model .empty

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- Exact native events come from the same actual allocation, retained cells and loading word. -/
lemma measuredPreparation_events (N : Nat)
    (path : (prepare base noQuantum m ell width N).Path) :
    (prepare base noQuantum m ell width N).resourcePool path =
      measuredPreparationBudget width N := by
  change ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty (Physical.qubits width).toQuantum
        BitWord.model .empty ++
      ((MeasurementCells.allocate (model := model) (bankContext base noQuantum width) 2
        (resultBits m ell + (width - 2))).eventTrace path.2.1 ++
        (Reload.code base noQuantum m ell width N).eventTrace path.2.2)) = _
  have cellsEmpty := MeasurementCells.allocate_eventTrace (model := model)
    (bankContext base noQuantum width) 2 (resultBits m ell + (width - 2)) path.2.1
  rw [cellsEmpty, List.nil_append, ResourcePool.ofList_append]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (Physical.qubits width).toQuantum BitWord.model .empty +
    (Reload.code base noQuantum m ell width N).resourcePool path.2.2 = _
  exact congrArg₂ (fun left right : ResourcePool model => left + right)
    (measuredPreparation_bank_events width)
    (Reload.measuredReload_events base noQuantum m ell width N path.2.2)

/-- Only the actual native X word contributes quantum gate time during initial preparation. -/
lemma measuredPreparation_quantumTime (N : Nat)
    (path : (prepare base noQuantum m ell width N).Path) :
    (prepare base noQuantum m ell width N).quantumTime path ≤
      EncodedBit.Word.BasisLoad.xCount (seedLabel width N) := by
  let allocated : Circuit model base (bankContext base noQuantum width) :=
    .prepareZero base base.canonicalFreshKey (Physical.qubits width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (preparationDisjoint base noQuantum width)
  let retained : Circuit model (bankContext base noQuantum width)
      (context base noQuantum m ell width) :=
    MeasurementCells.allocate (model := model) (bankContext base noQuantum width) 2
      (resultBits m ell + (width - 2))
  have allocatedTime : allocated.quantumTime path.1 = 0 :=
    Circuit.quantumTime_prepareZero base base.canonicalFreshKey (Physical.qubits width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (preparationDisjoint base noQuantum width) path.1
  have retainedTime : retained.quantumTime path.2.1 = 0 :=
    MeasurementCells.allocate_depth (model := model) (bankContext base noQuantum width) 2
      (resultBits m ell + (width - 2)) Resource.Event.quantumDuration path.2.1
  have actual : (prepare base noQuantum m ell width N).quantumTime path =
      allocated.quantumTime path.1 +
        (retained.quantumTime path.2.1 +
          (Reload.code base noQuantum m ell width N).quantumTime path.2.2) := rfl
  rw [actual, allocatedTime, retainedTime, Nat.zero_add, Nat.zero_add]
  exact Reload.measuredReload_quantumTime base noQuantum m ell width N path.2.2

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
