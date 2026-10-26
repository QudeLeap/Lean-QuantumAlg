/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Actual compute, finite-word copy and complete native uncomputation

The select circuit is supplied as a real native program with its exact
prepared-state action. The preparation must commute with the complete
original output-word XOR, including every temporary carry and work bit.
No mathematical readout or function is compiled into a free instruction.
-/

namespace QuantumAlg.EncodedBit.WordCompute

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete native prepare and its actual adjoint surround the paid word-copy circuit. -/
def program (prepare select : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  PredicateCompute.program prepare select

/-- The real native sandwich writes the selected finite word and restores its whole complement. -/
lemma program_apply_encoded_ket (prepare select : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum) (prepared : Data → Data)
    (output : Word encoding width) (constant : Fin (2 ^ width)) (selected : Bool)
    (environment : OracleModel.empty.Interpretation)
    (prepareActual : UnitaryCircuit.Realizes encoding prepare environment prepared)
    (state : Data)
    (selectActual : select.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          (encoding.encode (prepared state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (if selected then Word.xorConstantStep output constant (prepared state)
          else prepared state))))
    (commute : prepared (Word.xorConstantStep output constant state) =
      Word.xorConstantStep output constant (prepared state)) :
    (program prepare select).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (encoding.encode (if selected then Word.xorConstantStep output constant state
          else state))) := by
  rw [program, PredicateCompute.program, UnitaryCircuit.applyNormalized_seq,
    prepareActual.apply_encoded_ket, UnitaryCircuit.applyNormalized_seq, selectActual]
  cases selected
  · simp only [Bool.false_eq_true, if_false]
    exact PredicateCompute.restore prepare prepared environment prepareActual state
  · simp only [if_true]
    rw [← commute]
    exact PredicateCompute.restore prepare prepared environment prepareActual
      (Word.xorConstantStep output constant state)

end

end QuantumAlg.EncodedBit.WordCompute
