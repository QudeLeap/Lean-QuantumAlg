/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute

/-!
# Paid preparation and exact uncomputation around a complete state transform

The actual middle program must return the preparation of the complete
declared output state. This includes the entire source frame and every
temporary position, so a readout-only equality cannot discharge cleanup.
The final instruction is the actual native unitary adjoint of preparation.
-/

namespace QuantumAlg.EncodedBit.PredicateCompute

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Exact full-frame prepared output permits the same actual adjoint to restore all workspace. -/
lemma program_apply_transformed_ket (prepare middle : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) (prepared : Data → Data)
    (environment : OracleModel.empty.Interpretation)
    (prepareActual : UnitaryCircuit.Realizes encoding prepare environment prepared)
    (state output : Data)
    (middleActual : middle.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          (encoding.encode (prepared state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (prepared output)))) :
    (program prepare middle).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode output)) := by
  rw [program, UnitaryCircuit.applyNormalized_seq, prepareActual.apply_encoded_ket,
    UnitaryCircuit.applyNormalized_seq, middleActual]
  exact restore prepare prepared environment prepareActual output

end

end QuantumAlg.EncodedBit.PredicateCompute
