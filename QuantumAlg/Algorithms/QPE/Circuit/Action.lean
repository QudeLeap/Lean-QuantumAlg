/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Circuit.Matrix
import all QuantumAlg.Algorithms.QPE.Circuit.Matrix
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact joint eigenstate action of the actual QPE word

The original eigenstate survives the full native execution while the phase
prefix becomes the original inverse-Fourier readout. The equality retains the
complete normalized tensor state [Lin22, phaseestimation.tex:647-670].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

private lemma apply_mul {R : Register} (first second : UnitaryOperator R)
    (state : NormalizedVector R) :
    (first * second).apply state = first.apply (second.apply state) := by
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun vector : HilbertVector R => vector index)
    (UnitaryOperator.mul_applyVec first second state)

private lemma apply_identity {R : Register} (state : NormalizedVector R) :
    (1 : UnitaryOperator R).apply state = state := by
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun vector : HilbertVector R => vector index)
    (UnitaryOperator.one_applyVec (state : HilbertVector R))

/-- The same executed word produces the original phase readout and preserves the eigenstate. -/
lemma qpeNative_circuit_apply_eigenstate {systemWidth : Nat}
    (input : QPEEigenstateInput systemWidth) (phaseWidth : Nat) :
    ((circuit phaseWidth systemWidth).binaryMatrix (UnitarySource.interpretation
      input.unitary true)).apply
      ((NormalizedVector.ket (R := Qubits phaseWidth) 0).tensor input.eigenstate) =
        ((invQFT phaseWidth).apply (phaseState phaseWidth input.phase)).tensor
          input.eigenstate := by
  rw [qpeNative_circuit_binaryMatrix, apply_mul, apply_mul,
    UnitaryOperator.tensor_apply_tensor, WalshHadamard.hadamardLayerOperator_apply_zero,
    apply_identity, qpeControlledPowerOp_apply_uniform_eigenstate,
    UnitaryOperator.tensor_apply_tensor, apply_identity]

end

end QuantumAlg.QuantumPhaseEstimation.Native
