/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Resources.Events
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Resources.Events

/-!
# Complete independent native pools for the original five-table builder

The finite binary layers retain their seed, denominator rows, shared inverse
and extension rows. Final tangent inversion, five-column conversion and the
identity overwrite are charged separately. All loops remain symbolic; no
actual record or resource projection defines an allowance.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular Modular.NativePower
open scoped BigOperators

noncomputable section

/-- Native subtraction followed by one real denominator-array write. -/
def denominatorEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model :=
  ResourcePool.ofList (Field.Native.Shared.subTrace model width) +
    Accounting.rowWriteEnvelope model width length

/-- Independent native allowances of the ten original affine-extension slots. -/
def extensionSlotEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width length : Nat) : Fin 10 → ResourcePool model :=
  let sub := ResourcePool.ofList (Field.Native.Shared.subTrace model width)
  let multiply := multiplyEnvelope model width
  let write := Accounting.rowWriteEnvelope model width length
  ![sub, multiply, multiply, sub, sub, sub, multiply, sub, write, write]

/-- Complete native allowance for one original nonseed affine extension. -/
def extensionEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model := ∑ index, extensionSlotEnvelope model width length index

/-- Original add, subtraction and write for the negative tangent denominator. -/
def tangentSlotEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width length : Nat) : Fin 3 → ResourcePool model :=
  ![ResourcePool.ofList (Field.Native.Shared.addTrace model width),
    ResourcePool.ofList (Field.Native.Shared.subTrace model width),
    Accounting.rowWriteEnvelope model width length]

/-- All native coordinates of one tangent-denominator row. -/
def tangentEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model := ∑ index, tangentSlotEnvelope model width length index

/-- The fifteen actual final conversion slots, including all five array overwrites. -/
def finishSlotEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width length : Nat) : Fin 15 → ResourcePool model :=
  let add := ResourcePool.ofList (Field.Native.Shared.addTrace model width)
  let sub := ResourcePool.ofList (Field.Native.Shared.subTrace model width)
  let multiply := multiplyEnvelope model width
  let write := Accounting.rowWriteEnvelope model width length
  ![multiply, add, add, add, multiply, write, add, add, write, add, write,
    sub, write, sub, write]

/-- Complete native allowance for one five-column conversion. -/
def finishEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model := ∑ index, finishSlotEnvelope model width length index

/-- The first seed copies two rows; each later seed uses the original doubling envelope. -/
def seedEnvelope (model : ExecutionModel) [BitWord.Selected model] {width : Nat}
    (length : Nat) (spec : ModulusSpec width) (level : Nat) : ResourcePool model :=
  if level = 0 then 2 • Accounting.rowWriteEnvelope model width length else
    CoordinateFrame.doubleEnvelope model length spec

/-- Each binary layer pays every actual row and its one shared coefficient computation. -/
def layerEnvelope (model : ExecutionModel) [BitWord.Selected model] {width : Nat}
    (length : Nat) (spec : ModulusSpec width) (level : Nat) : ResourcePool model :=
  seedEnvelope model length spec level +
    ((2 ^ level - 1) • denominatorEnvelope model width length +
      (BatchFrame.envelope model length spec (2 ^ level - 1) +
        (2 ^ level - 1) • extensionEnvelope model width length))

/-- Finite independent event pool for all actual layers and the final table conversion. -/
def envelope (model : ExecutionModel) [BitWord.Selected model] {width : Nat}
    (window : Nat) (spec : ModulusSpec width) : ResourcePool model :=
  (∑ level : Fin window, layerEnvelope model (2 ^ window) spec level.val) +
    ((2 ^ window - 1) • tangentEnvelope model width (2 ^ window) +
      (BatchFrame.envelope model (2 ^ window) spec (2 ^ window - 1) +
        ((2 ^ window - 1) • finishEnvelope model width (2 ^ window) +
          5 • Accounting.rowWriteEnvelope model width (2 ^ window))))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat} (frame : TableFrame ctx width length)

/-- Both real seed copies use the original native vector-write coordinate. -/
lemma seedRow_pool (row : Fin length) (path : (frame.seedRow (model := model) row).Path) :
    (frame.seedRow (model := model) row).resourcePool path =
      2 • Accounting.rowWriteEnvelope model width length := by
  dsimp only [seedRow, Circuit.Path] at path ⊢
  rw [Accounting.seq_pool, Accounting.rowWrite_pool, Accounting.rowWrite_pool, two_nsmul]

/-- The five-table seed doubling uses the same fifteen original native allowances. -/
lemma doubleRow_pool_le (spec : ModulusSpec width) (source destination : Fin length)
    (path : (frame.doubleRow (model := model) spec source destination).Path) :
    (frame.doubleRow (model := model) spec source destination).resourcePool path ≤
      CoordinateFrame.doubleEnvelope model length spec := by
  unfold doubleRow CoordinateFrame.doubleEnvelope
  apply Circuit.forRange_pool_le_sum
  intro index selected
  fin_cases index <;> first
    | exact (Field.Native.Shared.sharedAddIntoWord_resourcePool _ _ _ _ selected).le
    | exact Field.Native.coefficientIntoWord_pool_le spec _ _ selected
    | exact (nativePower_scopedMultiply_pool _ _ _ _ selected).le
    | exact (Field.Native.Shared.sharedSubIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Accounting.rowWrite_pool _ _ _ selected).le

/-- Both actual denominator-row components retain their full pools. -/
lemma denominatorRow_pool (seed row : Fin length)
    (path : (frame.denominatorRow (model := model) seed row).Path) :
    (frame.denominatorRow (model := model) seed row).resourcePool path =
      denominatorEnvelope model width length := by
  dsimp only [denominatorRow, Circuit.Path] at path ⊢
  rw [Accounting.seq_pool, Field.Native.Shared.sharedSubIntoWord_resourcePool,
    Accounting.rowWrite_pool]
  rfl

/-- All actual affine-extension slots fit their independent native coordinate allowance. -/
lemma extendRow_pool_le (seed row destination : Fin length)
    (path : (frame.extendRow (model := model) seed row destination).Path) :
    (frame.extendRow (model := model) seed row destination).resourcePool path ≤
      extensionEnvelope model width length := by
  unfold extendRow extensionEnvelope
  apply Circuit.forRange_pool_le_sum
  intro index selected
  fin_cases index <;> first
    | exact (nativePower_scopedMultiply_pool _ _ _ _ selected).le
    | exact (Field.Native.Shared.sharedSubIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Accounting.rowWrite_pool _ _ _ selected).le

/-- Actual tangent-denominator construction retains add, subtraction and row write. -/
lemma tangentDenominatorRow_pool_le (row : Fin length)
    (path : (frame.tangentDenominatorRow (model := model) row).Path) :
    (frame.tangentDenominatorRow (model := model) row).resourcePool path ≤
      tangentEnvelope model width length := by
  unfold tangentDenominatorRow tangentEnvelope
  apply Circuit.forRange_pool_le_sum
  intro index selected
  fin_cases index <;> first
    | exact (Field.Native.Shared.sharedAddIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Field.Native.Shared.sharedSubIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Accounting.rowWrite_pool _ _ _ selected).le

/-- Every actual final conversion slot retains its complete original native labels. -/
lemma finishRow_pool_le (row : Fin length)
    (path : (frame.finishRow (model := model) row).Path) :
    (frame.finishRow (model := model) row).resourcePool path ≤
      finishEnvelope model width length := by
  unfold finishRow finishEnvelope
  apply Circuit.forRange_pool_le_sum
  intro index selected
  fin_cases index <;> first
    | exact (Field.Native.Shared.sharedAddIntoWord_resourcePool _ _ _ _ selected).le
    | exact (nativePower_scopedMultiply_pool _ _ _ _ selected).le
    | exact (Field.Native.Shared.sharedSubIntoWord_resourcePool _ _ _ _ selected).le
    | exact (Accounting.rowWrite_pool _ _ _ selected).le

/-- The identity row is explicitly overwritten in each of the five actual arrays. -/
lemma clearIdentityRow_pool_le (row : Fin length)
    (path : (frame.clearIdentityRow (model := model) row).Path) :
    (frame.clearIdentityRow (model := model) row).resourcePool path ≤
      5 • Accounting.rowWriteEnvelope model width length := by
  apply Accounting.range_pool_le
  intro index selected
  fin_cases index <;> exact (Accounting.rowWrite_pool _ _ _ selected).le

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

/-- The original static first-level choice selects its independent seed allowance. -/
lemma prepareSeed_pool_le (spec : ModulusSpec width) (level : Fin window) :
    ∀ path : (frame.prepareSeed (model := model) spec level).Path,
      (frame.prepareSeed (model := model) spec level).resourcePool path ≤
        seedEnvelope model (2 ^ window) spec level.val := by
  unfold prepareSeed seedEnvelope
  by_cases first : level.val = 0
  · rw [if_pos first, if_pos first]
    intro path
    exact (frame.seedRow_pool _ path).le
  · rw [if_neg first, if_neg first]
    exact frame.doubleRow_pool_le spec _ _

/-- One actual layer pays its seed, every denominator, shared inverse and every extension. -/
lemma layerCircuit_pool_le (spec : ModulusSpec width) (level : Fin window)
    (path : (frame.layerCircuit (model := model) spec level).Path) :
    (frame.layerCircuit (model := model) spec level).resourcePool path ≤
      layerEnvelope model (2 ^ window) spec level.val := by
  dsimp only [layerCircuit, Circuit.Path] at path ⊢
  have denominators := Accounting.range_pool_le (layerCount level)
    (fun index => frame.denominatorRow (model := model) (layerSeed window level)
      (oldRow level index)) (denominatorEnvelope model width (2 ^ window))
    (fun index selected => (frame.denominatorRow_pool _ _ selected).le) path.2.1
  have extensions := Accounting.range_pool_le (layerCount level)
    (fun index => frame.extendRow (model := model) (layerSeed window level)
      (oldRow level index) (newRow level index)) (extensionEnvelope model width (2 ^ window))
    (fun index selected => frame.extendRow_pool_le _ _ _ selected) path.2.2.2
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ _))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add (frame.prepareSeed_pool_le spec level path.1)
    (add_le_add denominators
      (add_le_add (frame.batch.circuit_pool_le spec (layerCount level) _ path.2.2.1) extensions))

/-- Every actual full builder path satisfies the complete independent finite native pool. -/
lemma circuit_pool_le (spec : ModulusSpec width)
    (path : (frame.circuit (model := model) spec).Path) :
    (frame.circuit (model := model) spec).resourcePool path ≤ envelope model window spec := by
  dsimp only [circuit, Circuit.Path] at path ⊢
  have layers := Circuit.forRange_pool_le_sum window (frame.layerCircuit (model := model) spec)
    (fun level : Fin window => layerEnvelope model (2 ^ window) spec level.val)
    (fun level selected => frame.layerCircuit_pool_le spec level selected) path.1
  have tangents := Accounting.range_pool_le (2 ^ window - 1)
    (fun index => frame.tangentDenominatorRow (model := model) (nonzeroRow window index))
    (tangentEnvelope model width (2 ^ window))
    (fun index selected => frame.tangentDenominatorRow_pool_le _ selected) path.2.1
  have finishes := Accounting.range_pool_le (2 ^ window - 1)
    (fun index => frame.finishRow (model := model) (nonzeroRow window index))
    (finishEnvelope model width (2 ^ window))
    (fun index selected => frame.finishRow_pool_le _ selected) path.2.2.2.1
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ (_ ++ _)))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add layers (add_le_add tangents
    (add_le_add (frame.batch.circuit_pool_le spec (2 ^ window - 1) _ path.2.2.1)
      (add_le_add finishes (frame.clearIdentityRow_pool_le _ path.2.2.2.2))))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
