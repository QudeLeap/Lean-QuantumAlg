/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QuditShift.Reset.Circuit
import all QuantumAlg.Components.QuditShift.Reset.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual finite reset and basis preparation on existing wires

Every stage measures once and executes the supplied shift from the stored
outcome directly to its prescribed basis value. The existing finite-sequence constructor
orders those stages. Cells are supplied by their actual writable references;
dimension-compatible references may alias, since each result is consumed
before the following stage. No allocation, release, or input-state promise
is introduced, including when the system list is empty.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

private instance sequenceCorrectionDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- Measure once and correct directly from the stored result to the prescribed basis value. -/
public def resetWireToBasis (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (allowAllocation : Bool := true) :
    Circuit (.quantum gates oracles) ctx ctx allowAllocation :=
  (Circuit.measureZ wire output).seq
    (.branch (.storage output.toCStorageRef) (fun outcome =>
      .unitary (realizations (value - outcome.toFin)).circuit))

/-- Execute the actual stages in the supplied finite order, permitting repeated wires and cells. -/
public def resetToBasisOn
    (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)
    (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) (allowAllocation : Bool := true) :
    Circuit (.quantum gates oracles) ctx ctx allowAllocation :=
  Circuit.forRange count (fun index =>
    resetWireToBasis (allowAllocation := allowAllocation) (wires index)
      (implementations (wires index))
      (outputs (wires index)) (label (wires index)))

/-- Reset and seed every existing physical system once, in its original finite-index order. -/
public def resetToBasis
    (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) (allowAllocation : Bool := true) :
    Circuit (.quantum gates oracles) ctx ctx allowAllocation :=
  resetToBasisOn (allowAllocation := allowAllocation) implementations ctx.systemCount id outputs
      label

end

end QuantumAlg.QuditShift
