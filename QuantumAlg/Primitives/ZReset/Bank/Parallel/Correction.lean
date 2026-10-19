/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Hadamard.Layer.Layout
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# A selected parallel X layer on the original bank

One stored outcome chooses either identity or a literal X on each wire.
The recursive tensor uses distinct physical identities, retaining every
selected native event while taking the maximum dependency depth. Placement
onto an arbitrary all-qubit bank preserves its exact wire order and requires
no quantum allocation or classical workspace inside the selected member.
-/

namespace QuantumAlg.ZReset.BankParallel.Correction

noncomputable section

open Gate.HadamardLayer (layout lastLayout)

/-- A single stored bit selects identity or its actual native X correction. -/
def last (oracles : OracleModel) (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model oracles (lastLayout width) :=
  if selected then
    Gate.singleQubitAt (lastLayout width) oracles Gate.XOp 0
      (Gate.HadamardLayer.hadamardLayer_last_dimension width)
  else
    UnitaryCircuit.identity AlgorithmGate.model oracles (lastLayout width)

/-- Count exactly the stored one outcomes, in physical position order. -/
def xCount : (width : Nat) → (Fin width → Bool) → Nat
  | 0, _ => 0
  | width + 1, selected =>
      xCount width (fun index => selected index.castSucc) +
        if selected (Fin.last width) then 1 else 0

/-- Distinct physical one-wire members execute in a single parallel layer. -/
def layer (oracles : OracleModel) :
    (width : Nat) → (Fin width → Bool) → UnitaryCircuit AlgorithmGate.model oracles (layout width)
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model oracles (layout 0)
  | width + 1, selected =>
      ((layer oracles width (fun index => selected index.castSucc)).tensor
        (last oracles width (selected (Fin.last width)))
        (Gate.HadamardLayer.hadamardLayer_layout_disjoint width)).castLayout
          (Gate.HadamardLayer.hadamardLayer_layout_append width)

/-- Identity contributes no event; a selected X contributes exactly one native event. -/
lemma last_eventTrace (oracles : OracleModel) (width : Nat) (selected : Bool) :
    (last oracles width selected).eventTrace =
      List.replicate (if selected then 1 else 0)
        (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .singleQubit) := by
  cases selected <;> rfl

/-- Parallel scheduling preserves every selected native correction in the actual trace. -/
lemma layer_eventTrace (oracles : OracleModel) (width : Nat) (selected : Fin width → Bool) :
    (layer oracles width selected).eventTrace =
      List.replicate (xCount width selected)
        (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .singleQubit) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [layer, UnitaryCircuit.castLayout_eventTrace,
        UnitaryCircuit.tensor_native_eventTrace, ih, last_eventTrace, xCount,
        List.replicate_add]

/-- The native ledger has exactly one X occurrence per selected stored outcome. -/
lemma layer_eventCost (oracles : OracleModel) (width : Nat) (selected : Fin width → Bool) :
    (layer oracles width selected).eventCost =
      xCount width selected • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, layer_eventTrace,
    ResourcePool.ofList_replicate]
  rfl

/-- There are no more selected corrections than physical bank positions. -/
lemma xCount_le (width : Nat) (selected : Fin width → Bool) : xCount width selected ≤ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [xCount]
      have earlier := ih (fun index => selected index.castSucc)
      split <;> omega

private lemma last_unitDepth_le (oracles : OracleModel) (width : Nat) (selected : Bool) :
    (last oracles width selected).evaluatedEventDepth (fun _ => 1) ≤ 1 := by
  cases selected with
  | false =>
      change 0 ≤ 1
      exact Nat.zero_le 1
  | true =>
      change 1 ≤ 1
      exact le_rfl

/-- Every selected correction layer has at most one quantum gate dependency. -/
lemma layer_unitDepth_le (oracles : OracleModel) (width : Nat) (selected : Fin width → Bool) :
    (layer oracles width selected).evaluatedEventDepth (fun _ => 1) ≤ 1 := by
  induction width with
  | zero =>
      change 0 ≤ 1
      exact Nat.zero_le 1
  | succ width ih =>
      rw [layer, UnitaryCircuit.castLayout_evaluatedEventDepth,
        UnitaryCircuit.tensor_native_evaluatedEventDepth]
      exact Nat.max_le.mpr ⟨ih _, last_unitDepth_le oracles width _⟩

/-- An empty bank executes the actual zero-event identity. -/
lemma layer_zero_unitDepth (oracles : OracleModel) (selected : Fin 0 → Bool) :
    (layer oracles 0 selected).evaluatedEventDepth (fun _ => 1) = 0 := rfl

variable {count : Nat} (physical : QuantumLayout count)
  (qubits : ∀ index, (physical.wire index).dimension = 2)

include qubits in
/-- The canonical order and the actual bank have the same local dimensions. -/
lemma dimensions (index : Fin count) :
    ((layout count).wire index).dimension =
      (physical.wire ((Function.Embedding.refl (Fin count)) index)).dimension :=
  (qubits index).symm

/-- The selected parallel word is placed onto all and only the original bank wires. -/
def program (oracles : OracleModel) (selected : Fin count → Bool) :
    UnitaryCircuit AlgorithmGate.model oracles physical :=
  UnitaryCircuit.placeAt (layout count) physical (Function.Embedding.refl _)
    (dimensions physical qubits) (layer oracles count selected)

/-- Physical placement does not add or hide any selected native event. -/
lemma program_eventCost (oracles : OracleModel) (selected : Fin count → Bool) :
    (program physical qubits oracles selected).eventCost =
      xCount count selected • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) := by
  rw [program, UnitaryCircuit.placeAt_eventCost, layer_eventCost]

/-- Classical operation and service grants preserve the exact selected native pool. -/
lemma program_eventCost_context (oracles : OracleModel) (selected : Fin count → Bool)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (program physical qubits oracles selected).eventCost operations services =
      xCount count selected • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) :=
          by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((program physical qubits oracles selected).eventCost operations services) =
      ResourcePool.count event (xCount count selected • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit))
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate => cases coordinate <;> simp [program_eventCost]
  | oracle _ => simp [program_eventCost]
  | classicalOperation _ => simp
  | classicalQuery _ => simp
  | preparation _ => simp
  | measurement _ => simp

/-- The same actual bank still has at most one correction layer. -/
lemma program_unitDepth_le (oracles : OracleModel) (selected : Fin count → Bool) :
    (program physical qubits oracles selected).evaluatedEventDepth (fun _ => 1) ≤ 1 := by
  rw [program, UnitaryCircuit.placeAt_evaluatedEventDepth]
  exact layer_unitDepth_le oracles count selected

end

end QuantumAlg.ZReset.BankParallel.Correction
