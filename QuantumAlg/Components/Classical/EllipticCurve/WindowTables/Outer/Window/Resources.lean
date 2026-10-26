/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Accounting

/-!
# Native-classical bound of one actual build/six-call/release window

The actual builder allowance is paid once inside the five-array lifetime.
Every subsequent real runtime query retains its own paid AND/XOR allowance.
No CNOT/classical sum or conversion is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open EncodedBit.WindowLookup EncodedBit.WindowLookup.RuntimeTable

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- One real table construction and exactly six actual runtime query-pair allowances. -/
def windowClassicalBudget (wordWidth lowWidth highRemaining : Nat) : Nat :=
  TableFrame.constructionBudget wordWidth (highRemaining + lowWidth + 1) +
    6 * runtimeCycleClassicalLimit wordWidth highRemaining lowWidth

/-- Every actual path pays its original builder and all six runtime parity computations. -/
lemma Frame.windowCircuit_classical_weight_le (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining)
    (path : (frame.windowCircuit (services := services) spec row column queries).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.windowCircuit spec row column queries).resourcePool path) ≤
        windowClassicalBudget wordWidth lowWidth highRemaining := by
  unfold Frame.windowCircuit withCells
  apply Accounting.allocation_weight_le
  intro inner cells distinct lift separated selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := table.circuit_classical_weight_le (model := Model) spec selected.1
  have queried : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Circuit.forRange 6 fun occurrence =>
        (queries lift occurrence).circuit
          (.storage (table.arrays.column (column occurrence)).toCStorageRef)).resourcePool
            selected.2) ≤ 6 * runtimeCycleClassicalLimit wordWidth highRemaining lowWidth := by
    apply Accounting.range_weight_le
    intro occurrence current
    change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (((queries lift occurrence).parameters
        (.storage (table.arrays.column (column occurrence)).toCStorageRef)).circuit.resourcePool
          current) ≤ _
    exact (((queries lift occurrence).parameters
      (.storage (table.arrays.column (column occurrence)).toCStorageRef)).separate_coordinates
        current).2
  exact Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _ selected
    built queried

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
