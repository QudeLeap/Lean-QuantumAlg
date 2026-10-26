/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute

/-!
# Pointwise inverse action of an actual native unitary word

A source-domain ket equality is sufficient: the native adjoint maps
that complete output back to the complete original input. This does
not require extending a partial arithmetic specification to invalid
metadata, and never takes an adjoint of a measurement instrument.
-/

namespace QuantumAlg.EncodedBit.PredicateCompute

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Actual unitary inversion retains every physical amplitude, including all temporary systems. -/
lemma dagger_apply_encoded_ket_of_apply (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum)
    (environment : OracleModel.empty.Interpretation) (state output : Data)
    (actual : body.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode output))) :
    (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode output))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode state)) := by
  rw [← actual]
  apply UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
  rw [UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

end

end QuantumAlg.EncodedBit.PredicateCompute
