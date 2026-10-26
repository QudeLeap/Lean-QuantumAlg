/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Resources

/-!
# Native classical coordinates of the actual small-base preparation

Two real input copies and every one of the sixteen doublings per window
are paid. These bounds count the actual native classical operations.
They introduce no exchange between classical operations and CNOT gates.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The two actual original coordinate copies emit two native instructions. -/
lemma seedCircuit_eventCount (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (row : Fin length) (path : (frame.seedCircuit (model := model) sourceX sourceY row).Path) :
    ((frame.seedCircuit (model := model) sourceX sourceY row).eventTrace path).length = 2 := by
  change ((BitWord.instruction (execution := model) (rowWriteOp frame.x row sourceX)).eventTrace
    path.1 ++ (BitWord.instruction (execution := model) (rowWriteOp frame.y row sourceY)).eventTrace
      path.2).length = 2
  rw [List.length_append, Accounting.instruction_eventCount, Accounting.instruction_eventCount]

/-- One next-base preparation pays all sixteen actual original doubling calls. -/
lemma baseStep_eventCount_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.baseStep (model := model) spec source destination).Path) :
    ((frame.baseStep (model := model) spec source destination).eventTrace path).length ≤
      16 * (30 * width + 127) := by
  have first := frame.doubleCircuit_eventCount_le spec source destination path.1
  have rest := Accounting.range_eventCount_le 15
    (fun _ => frame.doubleCircuit (model := model) spec destination destination)
    (fun _ => 30 * width + 127)
    (fun _ selected => frame.doubleCircuit_eventCount_le spec destination destination selected)
    path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at rest
  change ((frame.doubleCircuit (model := model) spec source destination).eventTrace path.1 ++
    (Circuit.forRange 15 (fun _ => frame.doubleCircuit spec destination destination)).eventTrace
      path.2).length ≤ _
  rw [List.length_append]
  omega

variable {baseCount : Nat} (frame : CoordinateFrame ctx width (baseCount + 1))

/-- The original small arrays are initialized once, then every actual window base is paid. -/
lemma prepareBases_eventCount_le (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (path : (frame.prepareBases (model := model) spec sourceX sourceY).Path) :
    ((frame.prepareBases (model := model) spec sourceX sourceY).eventTrace path).length ≤
      2 + baseCount * (16 * (30 * width + 127)) := by
  have seed := frame.seedCircuit_eventCount sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩ path.1
  have rest := Accounting.range_eventCount_le baseCount
    (fun index => frame.baseStep (model := model) spec index.castSucc index.succ)
    (fun _ => 16 * (30 * width + 127))
    (fun index selected => frame.baseStep_eventCount_le spec index.castSucc index.succ selected)
    path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at rest
  change ((frame.seedCircuit (model := model) sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩).eventTrace
    path.1 ++ (Circuit.forRange baseCount (fun index => frame.baseStep spec index.castSucc
      index.succ)).eventTrace path.2).length ≤ _
  rw [List.length_append, seed]
  exact Nat.add_le_add_left rest 2

/-- The same actual native-classical coordinate has the same independent operation ceiling. -/
lemma prepareBases_classical_weight_le (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (path : (frame.prepareBases (model := model) spec sourceX sourceY).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.prepareBases (model := model) spec sourceX sourceY).resourcePool path) ≤
        2 + baseCount * (16 * (30 * width + 127)) :=
  (Accounting.classical_weight_le_eventCount _ path).trans
    (frame.prepareBases_eventCount_le spec sourceX sourceY path)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
