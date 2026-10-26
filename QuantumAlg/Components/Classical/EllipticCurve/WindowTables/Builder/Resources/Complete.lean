/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Budget

/-!
# Complete actual five-array builder event ceiling

The actual finite layer loop and final conversion compose their original
instruction paths. Inversion is paid once per nonempty batch and once per
noninitial seed doubling. The resulting budget does not claim table-value
correctness; that requires the separate field/group and denominator laws.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- Actual first-seed copying and actual later doubling meet the independent per-level budget. -/
lemma prepareSeed_eventCount_le (spec : ModulusSpec width) (level : Fin window) :
    ∀ path : (frame.prepareSeed (model := model) spec level).Path,
      ((frame.prepareSeed (model := model) spec level).eventTrace path).length ≤
        seedBudget width level.val := by
  unfold prepareSeed seedBudget
  by_cases first : level.val = 0
  · rw [if_pos first, if_pos first]
    intro path
    exact (frame.seedRow_eventCount _ path).le
  · rw [if_neg first, if_neg first]
    exact frame.doubleRow_eventCount_le spec _ _

/-- Each actual binary layer pays its seed, denominator pass, shared inverse and extensions. -/
lemma layerCircuit_eventCount_le (spec : ModulusSpec width) (level : Fin window)
    (path : (frame.layerCircuit (model := model) spec level).Path) :
    ((frame.layerCircuit (model := model) spec level).eventTrace path).length ≤
      layerBudget width level.val := by
  dsimp only [layerCircuit, Circuit.Path] at path
  have seed := frame.prepareSeed_eventCount_le spec level path.1
  have denominators := Circuit.forRange_eventCount_le (layerCount level)
    (fun index => frame.denominatorRow (layerSeed window level) (oldRow level index)) 7
    (fun index selected => (frame.denominatorRow_eventCount _ _ selected).le) path.2.1
  have inverted := frame.batch.circuit_eventCount_le spec (layerCount level) _ path.2.2.1
  have extensions := Circuit.forRange_eventCount_le (layerCount level)
    (fun index => frame.extendRow (layerSeed window level) (oldRow level index)
      (newRow level index)) 41
    (fun index selected => frame.extendRow_eventCount_le _ _ _ selected) path.2.2.2
  change List.length (_ ++ (_ ++ (_ ++ _))) ≤ _
  simp only [List.length_append]
  change _ ≤ seedBudget width level.val + layerCount level * 7 +
    BatchFrame.eventBudget width (layerCount level) + layerCount level * 41
  omega

/-- All actual paths of the full five-array program meet the independent native event ceiling. -/
lemma circuit_eventCount_le (spec : ModulusSpec width)
    (path : (frame.circuit (model := model) spec).Path) :
    ((frame.circuit (model := model) spec).eventTrace path).length ≤
      constructionBudget width window := by
  dsimp only [circuit, Circuit.Path] at path
  have layers := Accounting.range_eventCount_le window (frame.layerCircuit spec)
    (fun level : Fin window => layerBudget width level.val)
    (fun level selected => frame.layerCircuit_eventCount_le spec level selected) path.1
  have tangent := Circuit.forRange_eventCount_le (2 ^ window - 1)
    (fun index => frame.tangentDenominatorRow (nonzeroRow window index)) 12
    (fun index selected => frame.tangentDenominatorRow_eventCount_le _ selected) path.2.1
  have inverted := frame.batch.circuit_eventCount_le spec (2 ^ window - 1) _ path.2.2.1
  have finalRows := Circuit.forRange_eventCount_le (2 ^ window - 1)
    (fun index => frame.finishRow (nonzeroRow window index)) 53
    (fun index selected => frame.finishRow_eventCount_le _ selected) path.2.2.2.1
  have identity := frame.clearIdentityRow_eventCount_le _ path.2.2.2.2
  change List.length (_ ++ (_ ++ (_ ++ (_ ++ _)))) ≤ _
  simp only [List.length_append]
  dsimp only [constructionBudget]
  omega

/-- Native classical work meets that same real instruction bound, without any CNOT conversion. -/
lemma circuit_classical_weight_le (spec : ModulusSpec width)
    (path : (frame.circuit (model := model) spec).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.circuit (model := model) spec).resourcePool path) ≤
        constructionBudget width window :=
  (Accounting.classical_weight_le_eventCount _ path).trans
    (frame.circuit_eventCount_le spec path)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
