/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Builder
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Separate actual quantum coordinates through the constructed-table scope

The paid classical builder contributes exactly zero at the selected
quantum coordinate. Only the six original actual runtime queries remain,
with their own physical gate bounds. No classical operation is converted
to a quantum gate in this projection.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace

noncomputable section

namespace QuantumAccounting

variable {model : ExecutionModel} (focus : Resource.Event model)
  {outer ctx : RuntimeCtx model.kind}

/-- Actual finite chronological composition retains its own coordinate bound on every path. -/
lemma range_count_le (count : Nat) (body : Fin count → Circuit model ctx ctx) (bound : Nat)
    (bounded : ∀ index path, ResourcePool.count focus ((body index).resourcePool path) ≤ bound)
    (path : (Circuit.forRange count body).Path) :
    ResourcePool.count focus ((Circuit.forRange count body).resourcePool path) ≤ count * bound := by
  induction count with
  | zero =>
      change ResourcePool.count focus 0 ≤ 0 * bound
      rw [ResourcePool.count_zero, Nat.zero_mul]
  | succ count ih =>
      have first := bounded 0 path.1
      have rest := ih _ (fun index => bounded index.succ) path.2
      change ResourcePool.count focus (ResourcePool.ofList (_ ++ _)) ≤ _
      rw [ResourcePool.ofList_append, ResourcePool.count_add, Nat.succ_mul]
      change ResourcePool.count focus ((body 0).resourcePool path.1) +
        ResourcePool.count focus ((Circuit.forRange count
          (fun index => body index.succ)).resourcePool path.2) ≤ count * bound + bound
      exact (Nat.add_le_add first rest).trans_eq (Nat.add_comm bound (count * bound))

/-- Real workspace scopes preserve each original native coordinate without extra events. -/
lemma allocation_count_le (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (lift : Transport outer inner) → cells.TransportSeparated lift → Circuit model inner inner)
    (bound : Nat)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (lift : Transport outer inner)
      (separated : cells.TransportSeparated lift)
      (path : (body cells distinct lift separated).Path),
      ResourcePool.count focus ((body cells distinct lift separated).resourcePool path) ≤ bound)
    (path : (withCellsFrom transport shapes body).Path) :
    ResourcePool.count focus ((withCellsFrom transport shapes body).resourcePool path) ≤ bound := by
  have actual := withCellsFrom_property transport shapes body
    (fun _ code => ∀ selected : code.Path, ResourcePool.count focus (code.resourcePool selected) ≤
      bound) (fun _ _ _ _ _ available => available) bounded
  exact actual path

end QuantumAccounting

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open EncodedBit.WindowLookup EncodedBit.WindowLookup.RuntimeTable

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- The identity embedding retains the actual query's independent native CNOT coordinate. -/
lemma QueryPlacement.circuit_cnot_count_le
    (placement : QueryPlacement encoding ctx wordWidth lowWidth highRemaining)
    (source : CInputRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    ∀ path : (placement.circuit (services := services) source).Path,
    ResourcePool.count (model := Model) (.gate .cnot)
      ((placement.circuit source).resourcePool path) ≤
        staticCycleCnotLimit wordWidth highRemaining lowWidth := by
  unfold QueryPlacement.circuit
  intro path
  rw [Circuit.resourcePool_embed]
  exact ((placement.parameters source).separate_coordinates path).1

/-- The same actual native Toffoli pool is retained through the identity embedding. -/
lemma QueryPlacement.circuit_toffoli_count_le
    (placement : QueryPlacement encoding ctx wordWidth lowWidth highRemaining)
    (source : CInputRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    ∀ path : (placement.circuit (services := services) source).Path,
    ResourcePool.count (model := Model) (.gate .toffoli)
      ((placement.circuit source).resourcePool path) ≤
        (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
          (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4)) := by
  unfold QueryPlacement.circuit
  intro path
  rw [Circuit.resourcePool_embed]
  exact (placement.parameters source).toffoli_count_le path

/-- The original result systems are measured exactly once per actual query pair. -/
lemma QueryPlacement.circuit_measurement_count
    (placement : QueryPlacement encoding ctx wordWidth lowWidth highRemaining)
    (source : CInputRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    ∀ path : (placement.circuit (services := services) source).Path,
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
      ((placement.circuit source).resourcePool path) = wordWidth := by
  unfold QueryPlacement.circuit
  intro path
  rw [Circuit.resourcePool_embed]
  exact (placement.parameters source).measurement_count path

/-- Every actual table scope retains the independent quantum bound of its six real query pairs. -/
lemma Frame.windowCircuit_quantum_count_le (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining)
    (focus : Resource.Event Model)
    (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate) (bound : Nat)
    (queryBound : ∀ {inner : RuntimeCtx .quantum}
      (placement : QueryPlacement encoding inner wordWidth lowWidth highRemaining)
      (source : CInputRef inner
        (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
      (selected : (placement.circuit (services := services) source).Path),
      ResourcePool.count focus ((placement.circuit source).resourcePool selected) ≤ bound)
    (path : (frame.windowCircuit (services := services) spec row column queries).Path) :
    ResourcePool.count focus
      ((frame.windowCircuit spec row column queries).resourcePool path) ≤ 6 * bound := by
  unfold Frame.windowCircuit withCells
  apply QuantumAccounting.allocation_count_le
  intro inner cells distinct lift separated selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := QuantumAccounting.builder_count_zero focus nativeFree table spec selected.1
  have queried := QuantumAccounting.range_count_le focus 6
    (fun occurrence => (queries lift occurrence).circuit
      (.storage (table.arrays.column (column occurrence)).toCStorageRef)) bound
    (fun occurrence => queryBound (queries lift occurrence) _) selected.2
  rw [Circuit.resourcePool_count_seq, built, Nat.zero_add]
  exact queried

/-- CNOT gates retain their actual quantum coordinate separately from all classical work. -/
lemma Frame.windowCircuit_cnot_count_le (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining)
    (path : (frame.windowCircuit (services := services) spec row column queries).Path) :
    ResourcePool.count (model := Model) (.gate .cnot)
      ((frame.windowCircuit spec row column queries).resourcePool path) ≤
        6 * staticCycleCnotLimit wordWidth highRemaining lowWidth := by
  apply frame.windowCircuit_quantum_count_le spec row column queries (.gate .cnot)
    (fun _ same => by cases same) (staticCycleCnotLimit wordWidth highRemaining lowWidth)
    (fun placement source selected => ?_) path
  exact ((placement.parameters source).separate_coordinates selected).1

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
