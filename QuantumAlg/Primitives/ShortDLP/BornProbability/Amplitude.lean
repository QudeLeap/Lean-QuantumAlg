/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.BornProbability.Stage
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage.Readout

/-!
# Exact source amplitude of the declared short-DLP stage

The actual native preparation, fixed-model group query, and two native inverse
Fourier words produce the finite Fourier-fiber amplitude used by the source.
-/

namespace QuantumAlg.ShortDLP.BornProbability

open NormalizedVector

noncomputable section

private theorem outerProdEquiv_symm_tripleEquiv (params : RegisterParameters)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    (prodEquiv
      (m := firstBits params + params.ell)
      (n := params.workspaceBits)).symm
        (tripleEquiv params ((a, b), y)) =
      (prodEquiv (a, b), y) := by
  change (prodEquiv
      (m := firstBits params + params.ell)
      (n := params.workspaceBits)).symm
        (prodEquiv (prodEquiv (a, b), y)) = _
  rw [Equiv.symm_apply_apply]

/-- Each terminal basis amplitude of the actual declared stage is the source's
double inverse-Fourier sum over the encoded group-value fibers. -/
theorem declaredCircuit_amplitude {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (y : Fin (2 ^ params.workspaceBits)) :
    (DeclaredStage.circuit encoding g x).binaryMatrix.applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits params))
        (prodEquiv
          ((0 : Fin (2 ^ (firstBits params + params.ell))),
            (0 : Fin (2 ^ params.workspaceBits)))) :
        HilbertVector (Qubits (totalQubits params)))
      (tripleEquiv params ((j, k), y)) =
      circuitAmplitude encoding g x j k y := by
  rw [declared_circuit_apply_zeroVec]
  change HilbertOperator.applyVec
      ((DeclaredStage.readout encoding).binaryMatrix :
        HilbertOperator (Qubits (totalQubits params)))
      (postOracleVec encoding g x)
      (tripleEquiv params ((j, k), y)) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp (tripleEquiv params),
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [DeclaredStage.readout_binaryMatrix,
    UnitaryOperator.tensor_apply,
    outerProdEquiv_symm_tripleEquiv, Equiv.symm_apply_apply]
  rw [circuitAmplitude]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_eq_single y]
  · simp [postOracleVec, mul_assoc]
  · intro sourceWorkspace _hsource hne
    have hzero :
        (1 : UnitaryOperator (Qubits params.workspaceBits)) y sourceWorkspace = 0 := by
      change (if y = sourceWorkspace then (1 : Complex) else 0) = 0
      simp [Ne.symm hne]
    simp [postOracleVec, hzero]
  · simp

end

end QuantumAlg.ShortDLP.BornProbability
