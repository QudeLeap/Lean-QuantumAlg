/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Actual preparation, predicate copying, and unitary uncomputation

The same actual prepare body and its native adjoint surround the
actual predicate-selection circuit. Complete encoded-state semantics
require an explicit commutation proof, including every temporary carry.
The middle circuit is supplied as a real program with a ket action;
the mathematical predicate alone constructs no instruction.
-/

namespace QuantumAlg.EncodedBit.PredicateCompute

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Both forward preparation and its full actual adjoint execute in the emitted program. -/
def program (prepare select : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  prepare.seq (select.seq (prepare.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

private lemma restore (prepare : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) (prepared : Data → Data)
    (environment : OracleModel.empty.Interpretation)
    (actual : UnitaryCircuit.Realizes encoding prepare environment prepared) (state : Data) :
    (prepare.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (prepared state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode state)) := by
  rw [← actual.apply_encoded_ket state]
  apply UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
  rw [UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

/-- The full paid sandwich changes only its declared output and restores every prepared system. -/
lemma program_apply_encoded_ket (prepare select : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) (prepared : Data → Data)
    (output : EncodedBit encoding) (predicate : Data → Bool)
    (environment : OracleModel.empty.Interpretation)
    (prepareActual : UnitaryCircuit.Realizes encoding prepare environment prepared)
    (state : Data)
    (selectActual : select.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          (encoding.encode (prepared state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (if predicate state then output.flip (prepared state)
          else prepared state))))
    (commute : prepared (output.flip state) = output.flip (prepared state)) :
    (program prepare select).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (predicateFlip output predicate state))) := by
  rw [program, UnitaryCircuit.applyNormalized_seq, prepareActual.apply_encoded_ket,
    UnitaryCircuit.applyNormalized_seq, selectActual]
  simp only [predicateFlip]
  by_cases enabled : predicate state = true
  · rw [if_pos enabled, if_pos enabled, ← commute]
    exact restore prepare prepared environment prepareActual (output.flip state)
  · rw [if_neg enabled, if_neg enabled]
    exact restore prepare prepared environment prepareActual state

end

end QuantumAlg.EncodedBit.PredicateCompute
