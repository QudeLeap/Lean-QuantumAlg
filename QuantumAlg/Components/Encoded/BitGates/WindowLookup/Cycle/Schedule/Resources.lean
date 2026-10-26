/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Schedule
import all QuantumAlg.Core.Base.Accounting.OracleWeight

/-!
# Native resources of the actual three-round query schedule

The hypotheses certify each supplied actual full-window/tail-window circuit
against the independent problem budget. The same real circuit composition
then gives native Toffoli, CNOT plus classical-operation, actual MZ and quantum
depth limits. Separate point-arithmetic and table-construction work is absent
from this query fragment and must be added at integration.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.WindowSchedule

noncomputable section

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services
local notation "Code" => Circuit Model ctx ctx false

/-- Check the actual resource pool and depth of every path against an independent window budget. -/
def MeetsBudget (program : Code) (budget : WindowBudget) : Prop :=
  ∀ path,
    ResourcePool.count (model := Model) (.gate .toffoli) (program.resourcePool path) ≤
      budget.toffoli ∧
    ResourcePool.count (model := Model) (.gate .cnot) (program.resourcePool path) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (program.resourcePool path) ≤
        budget.cnotClassical ∧
    ResourcePool.count (model := Model) (.gate .singleQubit) (program.resourcePool path) ≤
      budget.singleQubit ∧
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+)) (program.resourcePool path) =
      budget.measurements ∧
    program.depth Resource.Event.quantumDuration path ≤ budget.quantumTime

private lemma indicator_count (focus : Resource.Event Model) (pool : ResourcePool Model) :
    ResourcePool.weightedCount (fun event => if event = focus then 1 else 0) pool =
      ResourcePool.count focus pool :=
  ResourcePool.weightedCount_eq_count_of_indicator _ focus (fun _ => rfl) pool

private lemma weighted_functions_add (first second : Resource.Event Model → Nat)
    (pool : ResourcePool Model) :
    ResourcePool.weightedCount (fun event => first event + second event) pool =
      ResourcePool.weightedCount first pool + ResourcePool.weightedCount second pool := by
  simp only [ResourcePool.weightedCount, Multiset.sum_map_add]

private def cnotClassicalWeight (event : Resource.Event Model) : Nat :=
  (if event = .gate .cnot then 1 else 0) + Resource.Event.classicalOperationWeight event

private lemma cnotClassical_weight (pool : ResourcePool Model) :
    ResourcePool.weightedCount cnotClassicalWeight pool =
      ResourcePool.count (model := Model) (.gate .cnot) pool +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool := by
  unfold cnotClassicalWeight
  rw [weighted_functions_add, indicator_count]

/-- Actual certified query circuits give the complete independent three-round native limits. -/
lemma threeRoundCircuit_resources (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code)
    (fullCertified : ∀ occurrence stream window,
      MeetsBudget (full occurrence stream window) (windowBudget 16))
    (tailCertified : ∀ occurrence stream, MeetsBudget (tail occurrence stream) (windowBudget 4))
    (path : (threeRoundCircuit full tail).Path) :
    ResourcePool.count (model := Model) (.gate .toffoli)
        ((threeRoundCircuit full tail).resourcePool path) ≤ 76084128 ∧
    ResourcePool.count (model := Model) (.gate .cnot)
        ((threeRoundCircuit full tail).resourcePool path) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((threeRoundCircuit full tail).resourcePool path) ≤ 29105013528 ∧
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
        ((threeRoundCircuit full tail).resourcePool path) = 156672 ∧
    (threeRoundCircuit full tail).depth Resource.Event.quantumDuration path ≤ 1440381312 := by
  have toffoli := threeRoundCircuit_weight_le full tail
    (fun event => if event = .gate .toffoli then 1 else 0)
    (windowBudget 16).toffoli (windowBudget 4).toffoli
    (fun occurrence stream window current => by
      rw [indicator_count]
      exact (fullCertified occurrence stream window current).1)
    (fun occurrence stream current => by
      rw [indicator_count]
      exact (tailCertified occurrence stream current).1) path
  have cnot := threeRoundCircuit_weight_le full tail cnotClassicalWeight
    (windowBudget 16).cnotClassical (windowBudget 4).cnotClassical
    (fun occurrence stream window current => by
      rw [cnotClassical_weight]
      exact (fullCertified occurrence stream window current).2.1)
    (fun occurrence stream current => by
      rw [cnotClassical_weight]
      exact (tailCertified occurrence stream current).2.1) path
  have measured := threeRoundCircuit_weight_eq full tail
    (fun event => if event = .measurement (2 : ℕ+) then 1 else 0) 256 256
    (fun occurrence stream window current => by
      rw [indicator_count]
      exact (fullCertified occurrence stream window current).2.2.2.1)
    (fun occurrence stream current => by
      rw [indicator_count]
      exact (tailCertified occurrence stream current).2.2.2.1) path
  have time := threeRoundCircuit_quantumTime_le full tail
    (windowBudget 16).quantumTime (windowBudget 4).quantumTime
    (fun occurrence stream window current =>
      (fullCertified occurrence stream window current).2.2.2.2)
    (fun occurrence stream current => (tailCertified occurrence stream current).2.2.2.2) path
  simp only [indicator_count] at toffoli measured
  rw [cnotClassical_weight] at cnot
  have toffoliLimit :
      18 * (2 * (16 * (windowBudget 16).toffoli + (windowBudget 4).toffoli)) = 76084128 := by
    norm_num [windowBudget, windowLowWidth]
  have cnotLimit :
      18 * (2 * (16 * (windowBudget 16).cnotClassical + (windowBudget 4).cnotClassical)) =
        29105013528 := by norm_num [windowBudget, windowLowWidth]
  have timeLimit :
      18 * (2 * (16 * (windowBudget 16).quantumTime + (windowBudget 4).quantumTime)) =
        1440381312 := by norm_num [windowBudget, windowLowWidth]
  exact ⟨toffoli.trans_eq toffoliLimit, cnot.trans_eq cnotLimit, measured,
    time.trans_eq timeLimit⟩

/-- The actual allocation-free query schedule retains exactly its existing caller context peak. -/
lemma threeRoundCircuit_spaces (full : Fin 18 → Fin 2 → Fin 16 → Code)
    (tail : Fin 18 → Fin 2 → Code) (path : (threeRoundCircuit full tail).Path) :
    (threeRoundCircuit full tail).peakResidentSpace path = ctx.residentSpace ∧
    (threeRoundCircuit full tail).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩

end

end QuantumAlg.EncodedBit.WindowLookup.WindowSchedule
