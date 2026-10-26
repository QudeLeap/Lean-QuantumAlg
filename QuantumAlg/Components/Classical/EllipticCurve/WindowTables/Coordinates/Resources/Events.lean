/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Indexed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting.Events

/-!
# Independent native pools for original coordinate-base preparation

The original fifteen doubling slots retain five additions, four products,
three subtractions, one actual coefficient computation and two array writes.
Both seed copies and every original sixteen-doubling transition are charged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular Modular.NativePower
open scoped BigOperators

noncomputable section

/-- Independent allowances in the literal fifteen-slot doubling order. -/
def doubleSlotEnvelope (model : ExecutionModel) [BitWord.Selected model]
    {width : Nat} (length : Nat) (spec : ModulusSpec width) : Fin 15 → ResourcePool model :=
  let add := ResourcePool.ofList (Field.Native.Shared.addTrace model width)
  let sub := ResourcePool.ofList (Field.Native.Shared.subTrace model width)
  let multiply := multiplyEnvelope model width
  let write := Accounting.rowWriteEnvelope model width length
  ![add, Field.Native.coefficientEnvelope model spec, multiply, add, add, add,
    multiply, add, multiply, sub, sub, multiply, sub, write, write]

/-- All native labels of one doubling, independent of records and storage placement. -/
def doubleEnvelope (model : ExecutionModel) [BitWord.Selected model]
    {width : Nat} (length : Nat) (spec : ModulusSpec width) : ResourcePool model :=
  ∑ index, doubleSlotEnvelope model length spec index

/-- Original copies and all sixteen doublings per subsequent window base. -/
def basesEnvelope (model : ExecutionModel) [BitWord.Selected model]
    {width : Nat} (length baseCount : Nat) (spec : ModulusSpec width) : ResourcePool model :=
  2 • Accounting.rowWriteEnvelope model width length +
    baseCount • (16 • doubleEnvelope model length spec)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat} (frame : CoordinateFrame ctx width length)

/-- Every actual doubling path satisfies the original fifteen independent slot allowances. -/
lemma doubleCircuit_pool_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleCircuit (model := model) spec source destination).Path) :
    (frame.doubleCircuit (model := model) spec source destination).resourcePool path ≤
      doubleEnvelope model length spec := by
  unfold doubleCircuit doubleEnvelope
  apply Circuit.forRange_pool_le_sum
  intro index selected
  fin_cases index <;> first
    | exact (Field.Native.Shared.sharedAddIntoWord_resourcePool _ _ _ _ selected).le
    | exact Field.Native.coefficientIntoWord_pool_le spec _ _ selected
    | exact (nativePower_scopedMultiply_pool _ _ _ _ selected).le
    | exact (Field.Native.Shared.sharedSubIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Accounting.rowWrite_pool _ _ _ selected).le

/-- Both initial coordinate writes retain their complete actual native coordinate. -/
lemma seedCircuit_pool (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (path : (frame.seedCircuit (model := model) sourceX sourceY row).Path) :
    (frame.seedCircuit (model := model) sourceX sourceY row).resourcePool path =
      2 • Accounting.rowWriteEnvelope model width length := by
  dsimp only [seedCircuit, Circuit.Path] at path ⊢
  rw [Accounting.seq_pool, Accounting.rowWrite_pool, Accounting.rowWrite_pool, two_nsmul]

/-- One base transition charges its first doubling and all fifteen subsequent doublings. -/
lemma baseStep_pool_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.baseStep (model := model) spec source destination).Path) :
    (frame.baseStep (model := model) spec source destination).resourcePool path ≤
      16 • doubleEnvelope model length spec := by
  have first := frame.doubleCircuit_pool_le spec source destination path.1
  have rest := Accounting.range_pool_le 15
    (fun _ => frame.doubleCircuit (model := model) spec destination destination)
    (doubleEnvelope model length spec)
    (fun _ selected => frame.doubleCircuit_pool_le spec destination destination selected) path.2
  have both := Accounting.seq_pool_le _ _ _ _ path first rest
  exact both.trans_eq (by rw [show 16 = 15 + 1 from rfl, add_nsmul, one_nsmul, add_comm])

/-- Arbitrary original row identities share the same independent complete base envelope. -/
lemma prepareBasesAt_pool_le {baseCount : Nat} (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length)
    (path : (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).Path) :
    (frame.prepareBasesAt (model := model) spec sourceX sourceY rows).resourcePool path ≤
      basesEnvelope model length baseCount spec := by
  have seed := (frame.seedCircuit_pool sourceX sourceY (rows 0) path.1).le
  have rest := Accounting.range_pool_le baseCount
    (fun index => frame.baseStep (model := model) spec (rows index.castSucc) (rows index.succ))
    (16 • doubleEnvelope model length spec)
    (fun index selected => frame.baseStep_pool_le spec (rows index.castSucc) (rows index.succ)
      selected) path.2
  exact Accounting.seq_pool_le _ _ _ _ path seed rest

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
