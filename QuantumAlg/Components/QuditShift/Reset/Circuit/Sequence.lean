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

Every stage executes the stored-result reset and then a real cyclic shift
to its prescribed basis value. The existing finite-sequence constructor
orders those stages. Cells are supplied by their actual writable references;
dimension-compatible references may alias, since each result is consumed
before the following stage. No allocation, release, or input-state promise
is introduced, including when the system list is empty.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- Reset one actual wire and apply its charged shift to the prescribed basis value. -/
public def resetWireToBasis (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension) : Circuit ctx ctx :=
  (resetCircuit wire output).seq (.unitary (program ctx.quantumLayout wire value)
    ((program_physical_idx ctx.quantumLayout wire value).trans ctx.quantumLayout_identities))

/-- Execute the actual stages in the supplied finite order, permitting repeated wires and cells. -/
public def resetToBasisOn (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) : Circuit ctx ctx :=
  Circuit.forRange count (fun index =>
    resetWireToBasis (wires index) (outputs (wires index)) (label (wires index)))

/-- Reset and seed every existing physical system once, in its original finite-index order. -/
public def resetToBasis
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) : Circuit ctx ctx :=
  resetToBasisOn ctx.systemCount id outputs label

end

end QuantumAlg.QuditShift
