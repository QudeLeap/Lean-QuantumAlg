/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Exact diagonal action between an actual reversible list and its inverse

Conjugation uses the literal forward list and the literal reversed list.
The theorem concerns the action of that same middle program and restores
the entire encoded label. Its event count includes both actual lists.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (layout : QubitLayout encoding.width) (oracles : OracleModel)

/-- Execute the actual list, the supplied unitary program, and the inverse list. -/
def conjugateProgram (gates : List (GateSpec encoding))
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  ((programList layout oracles gates).seq program).seq (programList layout oracles gates.reverse)

private theorem list_applyVec (gates : List (GateSpec encoding)) (state : Data) :
    (programList layout oracles gates).applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (NormalizedVector.ket (R := layout.toQuantum.register)
        (layout.basisEquiv.symm (encoding.encode (stepList gates state)))).vec :=
  congrArg NormalizedVector.vec ((realizesList layout oracles gates).apply_encoded_ket state)

/-- The actual diagonal middle action is evaluated after the actual forward permutation. -/
theorem conjugateProgram_applyVec_encoded_ket (gates : List (GateSpec encoding))
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum) (phase : Data → ℂ)
    (actual : ∀ state, program.applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      phase state •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec)
    (state : Data) :
    (conjugateProgram layout oracles gates program).applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      phase (stepList gates state) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  simp only [conjugateProgram, UnitaryCircuit.applyVec_seq]
  rw [list_applyVec, actual, UnitaryCircuit.applyVec_smul, list_applyVec,
    stepList_reverse_stepList]

/-- Both occurrences of every actual list element contribute to the same event trace. -/
theorem conjugateProgram_eventTrace_length (gates : List (GateSpec encoding))
    (program : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum) :
    (conjugateProgram layout oracles gates program).eventTrace.length =
      2 * gates.length + program.eventTrace.length := by
  simp only [conjugateProgram, UnitaryCircuit.seq_eventTrace, List.length_append,
    programList_eventTrace, List.length_map, List.length_reverse]
  omega

end

end QuantumAlg.EncodedBit.GateSpec
