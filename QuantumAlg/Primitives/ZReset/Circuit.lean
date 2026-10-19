/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Components.QuditShift.Reset.Circuit

/-!
# Reset a selected finite-dimensional system by measurement and a stored result

The circuit measures one physical system in the computational basis, writes
its outcome to the supplied classical register, and reads that register to
select a supplied exact negative-shift realization in the chosen native model.
The construction reuses the canonical component reset and its complete native
trace; the mathematical finite-dimensional shift grants no instruction.

The state update combines the projective measurement rule
[dW19, qcnotes.tex:5409] with unitary conjugation [dW19, qcnotes.tex:5405].
The local projector acts as the identity on all other systems and any external
reference [dW19, qcnotes.tex:5420].
-/

namespace QuantumAlg.ZReset

noncomputable section

variable {services : ClassicalOracleModel}

/-- Measure and read the stored result, then execute its supplied exact correction. -/
@[expose, implicit_reducible]
public def circuit {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty)
    (allowAllocation : Bool := true) :
    Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation :=
  QuditShift.resetCircuit (allowAllocation := allowAllocation) (services := services)
    wire output realizations operations

end

end QuantumAlg.ZReset
