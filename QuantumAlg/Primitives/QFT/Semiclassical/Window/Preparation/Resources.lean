/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime
import all QuantumAlg.Core.Execution.Time

/-!
# Paid native events and duration of the actual same-bank Hadamards

The existing program is a sequential native H word, so its exact event count
and duration are the symbolic active width. No new system, parallel schedule
or physical state preparation is substituted for that literal syntax.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {totalBits : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Every actual Hadamard is present in the same native event ledger. -/
lemma window_preparation_events (count : Nat) (ports : Ports ctx totalBits count) :
    (preparation count ports).eventCost = count •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [preparation, UnitaryCircuit.seq_eventCost, Gate.singleQubitAt_eventCost,
        ih ports.tail, add_nsmul, one_nsmul]
      exact add_comm _ _

/-- The literal sequential preparation has exactly one dependency step per active wire. -/
lemma window_preparation_unit_depth (count : Nat) (ports : Ports ctx totalBits count) :
    (preparation count ports).evaluatedEventDepth (fun _ => 1) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [preparation, UnitaryCircuit.evaluatedEventDepth_seq, ih ports.tail]
      change 1 + count = count + 1
      exact Nat.add_comm 1 count

/-- The same complete classical context does not alter any actual native quantum duration. -/
lemma window_preparation_quantumTime (count : Nat) (ports : Ports ctx totalBits count)
    (path : (Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) (preparation count ports)).Path) :
    (Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) (preparation count ports)).quantumTime path = count := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((preparation count ports).eventDepth operations services) = count
  rw [UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth,
    UnitaryCircuit.unitaryCircuit_unit_depth_classical_context, window_preparation_unit_depth]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
