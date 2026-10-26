/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-! # Default quantum duration of an actual sequential native bit-gate list -/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Each emitted X, CNOT and Toffoli contributes its real unit quantum duration. -/
lemma programList_quantumTime (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (gates : List (GateSpec encoding)) :
    (programList physical oracles gates).evaluatedEventDepth Resource.Event.quantumDuration =
      gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.evaluatedEventDepth_seq, ih]
      have head : (gate.program physical oracles).evaluatedEventDepth
          Resource.Event.quantumDuration = 1 := by
        cases gate <;> rfl
      rw [head, List.length_cons]
      omega

end

end QuantumAlg.EncodedBit.GateSpec
