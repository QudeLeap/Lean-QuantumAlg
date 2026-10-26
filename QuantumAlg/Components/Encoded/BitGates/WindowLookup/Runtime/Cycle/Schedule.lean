/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Parameters
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Schedule
import all QuantumAlg.Core.Base.Accounting.OracleWeight

/-!
# Actual runtime-array schedule with separate original coordinates

Every scheduled child is constructed from literal supplied frames and real
table storage, rather than a cost-certified abstract program. Each stream
executes sixteen full windows and a four-bit tail. Three rounds of six calls
retain all actual physical outcomes and chronological Store selections.
Point arithmetic and paid table construction are separate fragments.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- The complete query schedule constructs every child from its actual runtime-table placement. -/
def threeRoundCircuit
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1) :
    Circuit Model ctx ctx false :=
  WindowSchedule.threeRoundCircuit
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit)

private lemma indicator_count (focus : Resource.Event Model) (pool : ResourcePool Model) :
    ResourcePool.weightedCount (fun event => if event = focus then 1 else 0) pool =
      ResourcePool.count focus pool :=
  ResourcePool.weightedCount_eq_count_of_indicator _ focus (fun _ => rfl) pool

/-- The actual runtime query schedule has the independent quantum CNOT ceiling. -/
lemma threeRoundCircuit_cnot_count_le
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    ResourcePool.count (model := Model) (.gate .cnot)
      ((threeRoundCircuit full tail).resourcePool path) ≤ 19403437896 := by
  have actual := WindowSchedule.threeRoundCircuit_weight_le
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit)
    (fun event => if event = .gate .cnot then 1 else 0)
    (staticCycleCnotLimit 256 7 8) (staticCycleCnotLimit 256 1 2)
    (fun occurrence stream window current => by
      rw [indicator_count]
      exact ((full occurrence stream window).separate_coordinates
        (services := services) current).1)
    (fun occurrence stream current => by
      rw [indicator_count]
      exact ((tail occurrence stream).separate_coordinates (services := services) current).1)
    path
  rw [indicator_count] at actual
  exact actual.trans_eq runtimeCycle_threeRound_limits.1

/-- All real per-bit AND/XOR feedback remains in the separate native-classical ceiling. -/
lemma threeRoundCircuit_classical_weight_le
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((threeRoundCircuit full tail).resourcePool path) ≤ 19365397668 := by
  have actual := WindowSchedule.threeRoundCircuit_weight_le
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit)
    Resource.Event.classicalOperationWeight
    (runtimeCycleClassicalLimit 256 7 8) (runtimeCycleClassicalLimit 256 1 2)
    (fun occurrence stream window current =>
      ((full occurrence stream window).separate_coordinates (services := services) current).2)
    (fun occurrence stream current =>
      ((tail occurrence stream).separate_coordinates (services := services) current).2) path
  exact actual.trans_eq runtimeCycle_threeRound_limits.2

/-- Actual physical Toffolis follow from the literal native code of every scheduled child. -/
lemma threeRoundCircuit_toffoli_count_le
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    ResourcePool.count (model := Model) (.gate .toffoli)
      ((threeRoundCircuit full tail).resourcePool path) ≤ 76082904 := by
  have actual := WindowSchedule.threeRoundCircuit_weight_le
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit)
    (fun event => if event = .gate .toffoli then 1 else 0) 132086 38
    (fun occurrence stream window current => by
      rw [indicator_count]
      exact (full occurrence stream window).toffoli_count_le (services := services) current)
    (fun occurrence stream current => by
      rw [indicator_count]
      exact (tail occurrence stream).toffoli_count_le (services := services) current) path
  rw [indicator_count] at actual
  exact actual.trans_eq (by norm_num)

/-- The schedule retains all actual full-width physical outcome positions. -/
lemma threeRoundCircuit_measurement_count
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
      ((threeRoundCircuit full tail).resourcePool path) = 156672 := by
  have actual := WindowSchedule.threeRoundCircuit_weight_eq
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit)
    (fun event => if event = .measurement (2 : ℕ+) then 1 else 0) 256 256
    (fun occurrence stream window current => by
      rw [indicator_count]
      exact (full occurrence stream window).measurement_count (services := services) current)
    (fun occurrence stream current => by
      rw [indicator_count]
      exact (tail occurrence stream).measurement_count (services := services) current) path
  rw [indicator_count] at actual
  exact actual.trans (by norm_num)

/-- The actual eight-level mask trees retain all original parallel dependence depths. -/
lemma threeRoundCircuit_quantumTime_le
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (fullHeight : ∀ occurrence stream window, (full occurrence stream window).height = 8)
    (tailHeight : ∀ occurrence stream, (tail occurrence stream).height = 8)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    (threeRoundCircuit full tail).depth Resource.Event.quantumDuration path ≤ 834321528 := by
  have actual := WindowSchedule.threeRoundCircuit_quantumTime_le
    (fun occurrence stream window => (full occurrence stream window).circuit)
    (fun occurrence stream => (tail occurrence stream).circuit) 1448450 398
    (fun occurrence stream window current => by
      have bound := (full occurrence stream window).quantumTime_le (services := services) current
      simpa only [fullHeight, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] using
        bound)
    (fun occurrence stream current => by
      have bound := (tail occurrence stream).quantumTime_le (services := services) current
      simpa only [tailHeight, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] using
        bound)
    path
  exact actual.trans_eq (by norm_num)

/-- Actual allocation-free placement keeps the supplied existing context's exact peak. -/
lemma threeRoundCircuit_spaces
    (full : Fin 18 → Fin 2 → Fin 16 → CycleParameters encoding ctx 256 8 7)
    (tail : Fin 18 → Fin 2 → CycleParameters encoding ctx 256 2 1)
    (path : (threeRoundCircuit (services := services) full tail).Path) :
    (threeRoundCircuit full tail).peakResidentSpace path = ctx.residentSpace ∧
    (threeRoundCircuit full tail).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
