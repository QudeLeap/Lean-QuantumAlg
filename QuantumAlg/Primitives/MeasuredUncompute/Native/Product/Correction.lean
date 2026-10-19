/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Recompute
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program

/-!
# Measured-word correction using the actual variable-product circuit

The same three-word Gidney product computes the correction word, executes
the literal selected Z gates, and runs backwards. Both input words and
the accumulator are restored with the exact measured character. The
construction has no inverse oracle or supplied circuit-realization premise
[LYL+26, sec_point_add/sec_point_add.tex:85-105;
G17, paper.tex:319-334].

In measured multiplication or division, the surrounding native arithmetic
establishes that this recomputed product is the previously measured value.
The stored-result branch and its earlier Z writes are separate execution
composition obligations. These full-column equations also retain an
arbitrary external reference.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductCorrection

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MAU.Multiplication
open EncodedBit.Word

/-- Little-endian lenses address the existing third word of the actual product carrier. -/
def targetWord (width : Nat) : EncodedBit.Word (VariableGidney.encoding width) width where
  bit index := BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity width)
    (Accumulate.Gidney.encoding width)
    (BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity width)
      (BinaryLabelEncoding.finIdentity width) (VariableGidney.inputBit width index))

lemma targetWord_get (width : Nat) (index : Fin width)
    (state : VariableGidney.Registers width) :
    ((targetWord width).bit index).get state = state.2.2.val.testBit index.val :=
  VariableGidney.variableGidney_inputBit_get width index state.2.2

/-- Literal product, selected Z correction, and the same product's inverse. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) (mask : Fin width → Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (VariableGidney.encoding width).width).toQuantum :=
  Recompute.program (QubitLayout.canonical _) (VariableGidney.program width modulus)
    (targetWord width) mask

/-- Every complete input label retains precisely the recomputed product character. -/
lemma program_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (outcome : Fin (2 ^ width)) (state : VariableGidney.Registers width) :
    ((program width modulus (fun index => outcome.val.testBit index.val)).applyVec environment)
        (NormalizedVector.ket
          ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
            ((VariableGidney.encoding width).encode state))).vec =
      WalshHadamard.walshSign outcome
        (Nat.FixedWidth.variableWordPrefix modulus state.1 state.2.1 state.2.2 width) •
          (NormalizedVector.ket
            ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
              ((VariableGidney.encoding width).encode state))).vec := by
  rw [program, Recompute.recompute_phase_ket (QubitLayout.canonical _) _
    (VariableGidney.variableGidney_realizes width modulus)]
  rw [measuredCorrection_sign_walsh (targetWord width) _ _ outcome
    (fun index => targetWord_get width index _)]
  rfl

/-- The actual product and its inverse cancel the previously measured product's phase. -/
lemma program_cancels (width : Nat) (modulus : Fin (2 ^ width + 1))
    (outcome : Fin (2 ^ width)) (state : VariableGidney.Registers width) :
    ((program width modulus (fun index => outcome.val.testBit index.val)).applyVec environment)
        (WalshHadamard.walshSign outcome
          (Nat.FixedWidth.variableWordPrefix modulus state.1 state.2.1 state.2.2 width) •
            (NormalizedVector.ket
              ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
                ((VariableGidney.encoding width).encode state))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
          ((VariableGidney.encoding width).encode state))).vec := by
  rw [UnitaryCircuit.applyVec_smul, program_ket, smul_smul,
    WalshHadamard.walshSign_mul_self, one_smul]

/-- Every reference coordinate has the same exact complete-label phase correction. -/
lemma program_reference_entry (width : Nat) (modulus : Fin (2 ^ width + 1))
    (outcome : Fin (2 ^ width)) (state : VariableGidney.Registers width)
    {Reference : Register}
    (row : (QubitLayout.canonical (VariableGidney.encoding width).width).toQuantum.register.Index)
    (left right : Reference.Index) :
    UnitaryOperator.prodTensor
        ((program width modulus (fun index => outcome.val.testBit index.val)).matrix environment)
        (1 : UnitaryOperator Reference)
        (row, left)
        ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
          ((VariableGidney.encoding width).encode state), right) =
      if row = (QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
          ((VariableGidney.encoding width).encode state) ∧ left = right then
        WalshHadamard.walshSign outcome
          (Nat.FixedWidth.variableWordPrefix modulus state.1 state.2.1 state.2.2 width)
      else 0 := by
  rw [program, Recompute.recompute_reference_entry (QubitLayout.canonical _) _
    (VariableGidney.variableGidney_realizes width modulus)]
  rw [measuredCorrection_sign_walsh (targetWord width) _ _ outcome
    (fun index => targetWord_get width index _)]
  rfl

end

end QuantumAlg.MeasuredUncompute.NativeProductCorrection
