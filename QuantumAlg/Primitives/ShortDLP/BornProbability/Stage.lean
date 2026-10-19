/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.BornProbability.Oracle
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage.Semantics

/-!
# Prepared graph state of the declared short-DLP stage

The native Hadamard preparation followed by the model-owned query produces
the exact source graph vector. The inverse-Fourier readout and terminal Born
distribution are separate obligations.
-/

namespace QuantumAlg.ShortDLP.BornProbability

noncomputable section

/-- The actual preparation, in binary labels, produces the source's uniform
exponent vector with an untouched zero group workspace. -/
lemma declared_prepare_apply_zeroVec {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    ((DeclaredStage.prepare N params).binaryMatrix (declaredInterpretation encoding)).applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits params))
        (prodEquiv
          ((0 : Fin (2 ^ (firstBits params + params.ell))),
            (0 : Fin (2 ^ params.workspaceBits)))) :
        HilbertVector (Qubits (totalQubits params))) =
      preOracleVec params := by
  have normalized := congrArg
    (fun state : NormalizedVector (Qubits (totalQubits params)) =>
      (state : HilbertVector (Qubits (totalQubits params))))
    (DeclaredStage.prepare_binaryMatrix_apply_zero N params (declaredInterpretation encoding))
  simpa only [UnitaryOperator.apply_coe, NormalizedVector.coe_tensor,
    preOracleVec] using normalized

/-- Actual native preparation followed by the one granted group query is the
source graph vector before the two inverse-QFT readouts. -/
lemma declared_query_apply_preparationVec {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    ((declaredCircuit AlgorithmGate.model N params g x).binaryMatrix (declaredInterpretation
      encoding)).applyVec
      (((DeclaredStage.prepare N params).binaryMatrix (declaredInterpretation encoding)).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits params))
          (prodEquiv
            ((0 : Fin (2 ^ (firstBits params + params.ell))),
              (0 : Fin (2 ^ params.workspaceBits)))) :
          HilbertVector (Qubits (totalQubits params)))) =
      postOracleVec encoding g x := by
  rw [declared_prepare_apply_zeroVec, declaredCircuit_binaryMatrix]
  exact oracleOperator_apply_preOracle encoding g x

/-- The complete declared stage is the actual inverse-Fourier readout applied
to the proved source graph state, with the original workspace retained. -/
lemma declared_circuit_apply_zeroVec {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    ((DeclaredStage.circuit N params g x).binaryMatrix (declaredInterpretation encoding)).applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits params))
        (prodEquiv
          ((0 : Fin (2 ^ (firstBits params + params.ell))),
            (0 : Fin (2 ^ params.workspaceBits)))) :
        HilbertVector (Qubits (totalQubits params))) =
      ((DeclaredStage.readout N params).binaryMatrix (declaredInterpretation encoding)).applyVec
        (postOracleVec encoding g x) := by
  rw [DeclaredStage.circuit_binaryMatrix,
    UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    ← declaredCircuit_binaryMatrix AlgorithmGate.model encoding g x,
    declared_query_apply_preparationVec]

end

end QuantumAlg.ShortDLP.BornProbability
