/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.ExternalWord

/-!
# Reuse of actual source-guarded bodies under external selection

The original guard/body/guard endpoint determines the exact intermediate
body endpoint by injectivity of the original guard's real unitary.
Actual selected guards then execute around the same unchanged physical
body prefix. This is a compositional law, with no width-specific gate
expansion and no replacement of a real body by an assigned action.
-/

namespace QuantumAlg.EncodedBit.SelectedSandwich

noncomputable section

private lemma operator_cancel {R : Register} (operator : UnitaryOperator R)
    (state : NormalizedVector R) : (operator⁻¹).apply (operator.apply state) = state := by
  apply NormalizedVector.ext
  intro index
  change (operator⁻¹).applyVec (operator.applyVec state) index = _
  rw [← UnitaryOperator.mul_applyVec, inv_mul_cancel, UnitaryOperator.one_applyVec]

private lemma applyNormalized_injective {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) :
    Function.Injective (body.applyNormalized environment) := by
  intro left right same
  have restored := congrArg (fun state => ((body.matrix environment)⁻¹).apply state) same
  change ((body.matrix environment)⁻¹).apply ((body.matrix environment).apply left) =
    ((body.matrix environment)⁻¹).apply ((body.matrix environment).apply right) at restored
  simpa only [operator_cancel] using restored

variable {Data : Type} (source : BinaryLabelEncoding Data)

/-- Literal selected guards surround the unchanged original physical source body. -/
def program
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical source.width).toQuantum)
    (selectedGuard : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ExternalWord.encoding source).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ExternalWord.encoding source).width).toQuantum :=
  selectedGuard.seq ((UnitaryCircuit.onBinaryPrefix ExternalWord.flags.width body).seq
    selectedGuard)

/-- An actual old endpoint plus actual selected guards certifies the same complete source result. -/
lemma program_apply_encoded_ket
    (guard body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical source.width).toQuantum)
    (selectedGuard : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ExternalWord.encoding source).width).toQuantum)
    (environment : OracleModel.empty.Interpretation) (input before after output : Data)
    (flags : Bool × Bool)
    (first : guard.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode input))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode before)))
    (last : guard.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode after))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode output)))
    (original : (guard.seq (body.seq guard)).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode input))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode output)))
    (selectedFirst : selectedGuard.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ExternalWord.encoding source).encode (input, flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ExternalWord.encoding source).encode (before, flags))))
    (selectedLast : selectedGuard.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ExternalWord.encoding source).encode (after, flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ExternalWord.encoding source).encode (output, flags)))) :
    (program source body selectedGuard).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ExternalWord.encoding source).encode (input, flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ExternalWord.encoding source).encode (output, flags))) := by
  have middle : body.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode before))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (source.encode after)) := by
    apply applyNormalized_injective guard environment
    rw [last]
    simpa only [UnitaryCircuit.applyNormalized_seq, first] using original
  have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    source ExternalWord.flags body before after flags middle
  exact UnitaryCircuit.applyNormalized_seq_of_eq selectedFirst
    (UnitaryCircuit.applyNormalized_seq_of_eq lifted selectedLast)

end

end QuantumAlg.EncodedBit.SelectedSandwich
