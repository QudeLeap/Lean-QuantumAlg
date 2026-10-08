/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Actual raw result copies from the completed XGCD state

Three original native copies expose the previous remainder and its two
coefficients. The same record certifies the full quantum-reference state
equation and all caller-store writes. Fresh state allocation supplies the
separation from caller outputs; no coefficient or result is computed off-circuit.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The exact store after the original three final native copies. -/
def copyRawOutputsStore (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp
    (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd)).applyOp
    (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient)).applyOp
    (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
      (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient)

/-- Each complete quantum-reference block carries the actual three-copy store and path. -/
theorem xgcdNativeCopyRawOutputs_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (copyRawOutputs (model := model) cells outputs).execute Reference state =
      state.mapClassical (fun entry =>
      let result := copyRawOutputsStep (model := model) cells outputs entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [copyRawOutputs, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The copied values are the literal pre-copy state words, in original output order. -/
def rawResultStore (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (store : Store ctx) : Store ctx :=
  ((store.write outputs.gcd (store.read (GCD.cellRead (secondCell cells)))).write
    outputs.leftCoefficient (store.read (GCD.cellRead (secondLeftCell cells)))).write
      outputs.rightCoefficient (store.read (GCD.cellRead (secondRightCell cells)))

/-- Protected state reads make the actual native copies equal these three literal caller writes. -/
theorem xgcdNativeCopyRawOutputs_store (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (store : Store ctx)
    (gcdLeft : outputs.gcd.key ≠ (secondLeftCell cells).key)
    (gcdRight : outputs.gcd.key ≠ (secondRightCell cells).key)
    (leftRight : outputs.leftCoefficient.key ≠ (secondRightCell cells).key) :
    copyRawOutputsStore cells outputs store = rawResultStore cells outputs store := by
  have firstLeft := Store.read_write_other store outputs.gcd
    (secondLeftCell cells).toCStorageRef (store.read (GCD.cellRead (secondCell cells))) gcdLeft
  have firstRight := Store.read_write_other store outputs.gcd
    (secondRightCell cells).toCStorageRef (store.read (GCD.cellRead (secondCell cells))) gcdRight
  let first := store.write outputs.gcd (store.read (GCD.cellRead (secondCell cells)))
  have secondRight := Store.read_write_other first outputs.leftCoefficient
    (secondRightCell cells).toCStorageRef
    (first.read (GCD.cellRead (secondLeftCell cells))) leftRight
  change ((first.write outputs.leftCoefficient
    (first.read (GCD.cellRead (secondLeftCell cells)))).write outputs.rightCoefficient
      ((first.write outputs.leftCoefficient
        (first.read (GCD.cellRead (secondLeftCell cells)))).read
          (GCD.cellRead (secondRightCell cells)))) = _
  dsimp only [first, GCD.cellRead] at firstLeft firstRight secondRight ⊢
  rw [secondRight, firstRight, firstLeft]
  rfl

/-- Distinct caller destinations retain all three original raw state words simultaneously. -/
theorem xgcdNativeRawResultStore_values (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (distinct : outputs.Distinct) (store : Store ctx) :
    let final := rawResultStore cells outputs store
    final.read (GCD.cellRead outputs.gcd) = store.read (GCD.cellRead (secondCell cells)) ∧
      final.read (GCD.cellRead outputs.leftCoefficient) =
        store.read (GCD.cellRead (secondLeftCell cells)) ∧
      final.read (GCD.cellRead outputs.rightCoefficient) =
        store.read (GCD.cellRead (secondRightCell cells)) := by
  dsimp only [rawResultStore, GCD.cellRead]
  refine ⟨?_, ?_, ?_⟩
  · rw [Store.read_write_other _ outputs.rightCoefficient outputs.gcd.toCStorageRef _
        distinct.2.1.symm,
      Store.read_write_other _ outputs.leftCoefficient outputs.gcd.toCStorageRef _
        distinct.1.symm]
    exact Store.read_write_same _ _ _
  · rw [Store.read_write_other _ outputs.rightCoefficient outputs.leftCoefficient.toCStorageRef _
      distinct.2.2.symm]
    exact Store.read_write_same _ _ _
  · exact Store.read_write_same _ _ _

/-- Every structural read outside the three actual result destinations is unchanged. -/
theorem xgcdNativeCopyRawOutputs_read_other (cells : Cells ctx (stateShapes width))
    (outputs : RawOutputs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (gcdFree : outputs.gcd.key ∉ other.storageKeys)
    (leftFree : outputs.leftCoefficient.key ∉ other.storageKeys)
    (rightFree : outputs.rightCoefficient.key ∉ other.storageKeys) :
    (copyRawOutputsStore cells outputs store).read other = store.read other := by
  unfold copyRawOutputsStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
        (GCD.cellRead (secondRightCell cells)) outputs.rightCoefficient) other rightFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordUnary .copy (PureXGCD.executionCoefficientWidth width) ctx
        (GCD.cellRead (secondLeftCell cells)) outputs.leftCoefficient) other leftFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordUnary .copy width ctx (GCD.cellRead (secondCell cells)) outputs.gcd) other gcdFree]

/-- Fresh state allocation proves each state cell differs from every actual caller output. -/
theorem xgcdNativeRawOutput_state_separated {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    {shape : CShape} (output : CWriteRef outer shape) (index : Fin 7) :
    (transport.liftWrite output).key ≠ stateKey cells index := by
  have free := xgcdNativeState_input_separated cells transport separated
    (GCD.cellRead output) index
  intro same
  apply free
  rw [← same]
  change (transport.liftWrite output).key ∈ [(transport.liftWrite output).key]
  exact List.mem_singleton.mpr rfl

/-- Actual fresh-state placement discharges all source protection for the final native copies. -/
theorem xgcdNativeCopyRawOutputs_placed_store {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (outputs : RawOutputs outer width)
    (store : Store ctx) :
    copyRawOutputsStore cells (outputs.transport transport) store =
      rawResultStore cells (outputs.transport transport) store := by
  exact xgcdNativeCopyRawOutputs_store cells (outputs.transport transport) store
    (xgcdNativeRawOutput_state_separated cells transport separated outputs.gcd 4)
    (xgcdNativeRawOutput_state_separated cells transport separated outputs.gcd 5)
    (xgcdNativeRawOutput_state_separated cells transport separated outputs.leftCoefficient 5)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
