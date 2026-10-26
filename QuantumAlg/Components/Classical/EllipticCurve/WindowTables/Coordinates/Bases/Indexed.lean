/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Resources

/-!
# Actual small-base preparation at existing physical row indices

A public static row family selects the same original two coordinate
arrays. The program executes two paid copies and sixteen real doublings
per next row. Two disjoint seventeen-row families can therefore retain
both original points in the same X/Y arrays of length thirty-four.
There is no writable classical view, extra array or executed recoding.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular
open scoped BigOperators

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length baseCount : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Original paid base preparation at statically supplied existing row identities. -/
def prepareBasesAt (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) : Circuit model ctx ctx :=
  .seq (frame.seedCircuit sourceX sourceY (rows ⟨0, Nat.zero_lt_succ _⟩))
    (Circuit.forRange baseCount (fun index =>
      frame.baseStep spec (rows index.castSucc) (rows index.succ)))

/-- The real two copies and all original doubling calls consume their actual predecessor Stores. -/
def prepareBasesAtRecord (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).Path :=
  Circuit.sequenceRecord (frame.seedCircuit sourceX sourceY (rows ⟨0, Nat.zero_lt_succ _⟩))
    (Circuit.forRange baseCount (fun index =>
      frame.baseStep spec (rows index.castSucc) (rows index.succ)))
    (frame.seedRecord sourceX sourceY (rows ⟨0, Nat.zero_lt_succ _⟩))
    (Circuit.forRangeRecord baseCount (fun index =>
      frame.baseStep spec (rows index.castSucc) (rows index.succ))
      (fun index => frame.baseStepRecord spec (rows index.castSucc) (rows index.succ) environment))

/-- Static row selection preserves the original complete actual history and arbitrary Reference. -/
lemma prepareBasesAt_execute (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).execute environment Reference
      state = state.mapClassical (fun entry =>
        let result := frame.prepareBasesAtRecord spec sourceX sourceY rows environment
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord
  · exact frame.seedCircuit_execute sourceX sourceY (rows ⟨0, Nat.zero_lt_succ _⟩) environment
  · exact Circuit.execute_forRangeRecord baseCount _ environment _
      (fun index => frame.baseStep_execute spec (rows index.castSucc) (rows index.succ) environment)

/-- Every actual native operation is paid independently of the chosen existing row identities. -/
lemma prepareBasesAt_eventCount_le (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length)
    (path : (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).Path) :
    ((frame.prepareBasesAt (model := model) spec sourceX sourceY rows).eventTrace path).length ≤
      2 + baseCount * (16 * (30 * width + 127)) := by
  have seed := frame.seedCircuit_eventCount sourceX sourceY (rows ⟨0, Nat.zero_lt_succ _⟩) path.1
  have rest := Accounting.range_eventCount_le baseCount
    (fun index => frame.baseStep (model := model) spec (rows index.castSucc) (rows index.succ))
    (fun _ => 16 * (30 * width + 127))
    (fun index selected => frame.baseStep_eventCount_le spec (rows index.castSucc)
      (rows index.succ) selected) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at rest
  change ((frame.seedCircuit (model := model) sourceX sourceY
    (rows ⟨0, Nat.zero_lt_succ _⟩)).eventTrace path.1 ++
    (Circuit.forRange baseCount (fun index => frame.baseStep spec (rows index.castSucc)
      (rows index.succ))).eventTrace path.2).length ≤ _
  rw [List.length_append, seed]
  exact Nat.add_le_add_left rest 2

/-- Static physical row selection retains the same paid native-classical coordinate. -/
lemma prepareBasesAt_classical_weight_le (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length)
    (path : (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.prepareBasesAt (model := model) spec sourceX sourceY rows).resourcePool path) ≤
        2 + baseCount * (16 * (30 * width + 127)) :=
  (Accounting.classical_weight_le_eventCount _ path).trans
    (frame.prepareBasesAt_eventCount_le spec sourceX sourceY rows path)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
