/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Time
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program

/-!
# Actual quantum time within one constructed-table lifetime

The unchanged original builder has zero native quantum duration. The six
physical query pairs retain their own actual parallel mask layers and
supplied tree height, including the paid measured-unlookup feedback.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open EncodedBit.WindowLookup EncodedBit.WindowLookup.RuntimeTable

noncomputable section

/-- Actual load/unlookup depth allowance at the supplied native tree height. -/
def queryQuantumLimit (highRemaining lowWidth height : Nat) : Nat :=
  (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
    2 * 2 ^ (highRemaining + lowWidth) * (2 * height + 1)) +
      (2 + 2 * (2 ^ lowWidth + lowWidth) +
        ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8))

private lemma queryQuantumLimit_mono (highRemaining lowWidth first second : Nat)
    (heights : first ≤ second) :
    queryQuantumLimit highRemaining lowWidth first ≤ queryQuantumLimit highRemaining lowWidth
      second := by
  unfold queryQuantumLimit
  gcongr

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- The actual build and six query pairs retain their own physical dependency depths. -/
lemma Frame.windowCircuit_quantumTime_le (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining)
    (height : Nat)
    (heights : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner) occurrence,
      (queries lift occurrence).height ≤ height)
    (path : (frame.windowCircuit (services := services) spec row column queries).Path) :
    (frame.windowCircuit spec row column queries).depth Resource.Event.quantumDuration path ≤
      6 * queryQuantumLimit highRemaining lowWidth height := by
  unfold Frame.windowCircuit withCells
  apply withCellsFrom_depth_le
  intro inner cells distinct lift separated selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := QuantumAccounting.quantumTime_zero (table.circuit (model := Model) spec)
    (fun focus nativeFree => QuantumAccounting.builder_count_zero focus nativeFree table spec)
    selected.1
  change (table.circuit (model := Model) spec).depth Resource.Event.quantumDuration selected.1 +
    _ ≤ _
  rw [show (table.circuit (model := Model) spec).depth
    Resource.Event.quantumDuration selected.1 = 0 from built, Nat.zero_add]
  apply QuantumAccounting.range_depth_le
  intro occurrence current
  let placement := queries lift occurrence
  let source := CInputRef.storage (table.arrays.column (column occurrence)).toCStorageRef
  have actual := (placement.parameters source).quantumTime_le (services := services) current
  exact actual.trans (queryQuantumLimit_mono highRemaining lowWidth placement.height height
    (heights lift occurrence))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
