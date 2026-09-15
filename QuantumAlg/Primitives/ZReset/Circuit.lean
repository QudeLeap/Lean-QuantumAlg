/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Components.QuditShift

/-!
# Reset a selected finite-dimensional system by measurement and a stored result

This circuit measures one physical system in the computational basis, writes
its outcome to the supplied classical register, reads that register, and
applies the negative cyclic shift selected by the actual stored value.

The state update combines the projective measurement rule
[dW19, qcnotes.tex:5409] with unitary conjugation [dW19, qcnotes.tex:5405].
The local projector acts as the identity on all other systems and any external
reference [dW19, qcnotes.tex:5420]. The same circuit records the measurement,
classical selection, and declared shift in its resource interpretation.
-/

namespace QuantumAlg.ZReset

noncomputable section

/-- One syntax tree measures, writes and reads its result, then applies its negative shift. -/
public def circuit {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) : Circuit ctx ctx :=
  .seq (.measureZ wire output)
    (.branch (.storage output.toCStorageRef) (fun result =>
      .unitary (QuditShift.program ctx.quantumLayout wire (-result.toFin))
        ((QuditShift.quditShift_program_physical_idx ctx.quantumLayout wire (-result.toFin)).trans
          (RuntimeCtx.runtimeCtx_quantumLayout_identities ctx))))

end

end QuantumAlg.ZReset
