/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Gates.SingleQubit.Diagonal
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Native Pauli Z and exact global phase

Both operations use the default model's arbitrary one-qubit declaration at
the original encoded wire. The exact minus-identity operator is one native
instruction. No projective equivalence discards its phase before control.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The native one-qubit Z operator on the supplied physical encoded wire. -/
def pauliZ (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  Gate.singleQubitAt layout.toQuantum oracles Gate.ZOp target.wire rfl

/-- Pauli Z contributes one default-model single-qubit event. -/
theorem pauliZ_eventTrace (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (target.pauliZ layout oracles).eventTrace = [.gate .singleQubit] := rfl

private theorem z_diagonal (row column : Fin 2) :
    Gate.ZOp row column =
      if row = column then (if column = 1 then (-1 : ℂ) else 1) else 0 := by
  fin_cases row <;> fin_cases column <;> rfl

private theorem encoded_bit (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (state : Data) :
    layout.basisEquiv.symm (encoding.encode state) target.wire =
      finTwoEquiv.symm (target.get state) :=
  target.targetBasisEquiv_first state

/-- Exact phase on every full physical ket of the original semantic encoding. -/
theorem pauliZ_applyVec_encoded_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) (state : Data) :
    (target.pauliZ layout oracles).applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (if target.get state then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  have actual := Gate.singleQubitAt_diagonal_applyVec_ket layout oracles Gate.ZOp
    (fun value => if value = 1 then (-1 : ℂ) else 1) z_diagonal target.wire
    (layout.basisEquiv.symm (encoding.encode state))
  rw [encoded_bit] at actual
  unfold pauliZ UnitaryCircuit.applyVec
  cases value : target.get state <;> simpa [value, finTwoEquiv] using actual

private def globalMinusOperator : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(-1 : ℂ), 0; 0, -1] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Matrix.star_apply])

private theorem globalMinus_diagonal (row column : Fin 2) :
    globalMinusOperator row column = if row = column then (-1 : ℂ) else 0 := by
  fin_cases row <;> fin_cases column <;> rfl

/-- The default model executes the exact one-qubit minus identity as one native gate. -/
def globalMinus (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  Gate.singleQubitAt layout.toQuantum oracles globalMinusOperator target.wire rfl

/-- The complete encoded input is restored with exact phase minus one. -/
theorem globalMinus_applyVec_encoded_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) (state : Data) :
    (target.globalMinus layout oracles).applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      -(NormalizedVector.ket (R := layout.toQuantum.register)
        (layout.basisEquiv.symm (encoding.encode state))).vec := by
  have actual := Gate.singleQubitAt_diagonal_applyVec_ket layout oracles globalMinusOperator
    (fun _ => (-1 : ℂ)) globalMinus_diagonal target.wire
    (layout.basisEquiv.symm (encoding.encode state))
  unfold globalMinus UnitaryCircuit.applyVec
  simpa only [neg_one_smul] using actual

/-- The exact phase correction executes one native single-qubit gate. -/
theorem globalMinus_eventTrace_length (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    (target.globalMinus layout oracles).eventTrace.length = 1 := rfl

end

end QuantumAlg.EncodedBit
