/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Primitives.WalshHadamard.Initialization
import all QuantumAlg.Primitives.WalshHadamard.Construction.Matrix
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Components.Gates.SingleQubit.Last.Binary
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow

/-!
# From fixed zero input to the original Walsh query state

The actual target X converts the zero input to |0^n>|1>. The same following
query word therefore produces the original full joint state, including its
target factor [dW19, qcnotes.tex:1193,1245].
-/

namespace QuantumAlg.WalshHadamard.Native

noncomputable section

private lemma zero_tensor (width : Nat) :
    (NormalizedVector.ket (R := Qubits width) 0).tensor
      (NormalizedVector.ket (R := Qubits 1) 0) =
        NormalizedVector.ket (R := Qubits (width + 1)) 0 := by
  rw [NormalizedVector.tensor_ket]
  congr 1

/-- The actual final-wire X implements exactly identity tensor X, with no phase loss. -/
lemma walshNative_targetFlip_binaryMatrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((targetFlip oracles width).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits width)).tensor Gate.XOp := by
  exact Gate.singleQubitAt_last_binaryMatrix oracles width Gate.XOp environment

/-- One actual native X prepares the required target from the fixed zero input. -/
lemma walshNative_targetFlip_apply_zero (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((targetFlip oracles width).binaryMatrix environment).apply
      (NormalizedVector.ket (R := Qubits (width + 1)) 0) = input width := by
  rw [walshNative_targetFlip_binaryMatrix, ← zero_tensor, UnitaryOperator.tensor_apply_tensor]
  have first : (1 : UnitaryOperator (Qubits width)).apply
      (NormalizedVector.ket (R := Qubits width) 0) =
        NormalizedVector.ket (R := Qubits width) 0 := by
    apply NormalizedVector.ext
    intro index
    change ((1 : UnitaryOperator (Qubits width)).applyVec
      (NormalizedVector.ket (R := Qubits width) 0 : HilbertVector (Qubits width))) index = _
    rw [UnitaryOperator.one_applyVec]
  have target : Gate.XOp.apply (NormalizedVector.ket (R := Qubits 1) 0) =
      NormalizedVector.ket (R := Qubits 1) 1 := by
    rw [Gate.XOp, UnitaryOperator.ofPerm_apply_ket]
    congr 1
  rw [first, target]
  rfl

/-- The actual word after zero preparation yields the original complete Walsh final state. -/
lemma walshNative_zeroInputProgram_apply_zero {width : Nat}
    (function : Fin (2 ^ width) → Bool) :
    ((zeroInputProgram width).binaryMatrix (XorOracle.interpretation function)).apply
      (NormalizedVector.ket (R := Qubits (width + 1)) 0) = finalJointState function := by
  rw [zeroInputProgram, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  have composed :
      (((queryPipeline width).binaryMatrix (XorOracle.interpretation function)) *
        ((targetFlip (XorOracle.model width) width).binaryMatrix
          (XorOracle.interpretation function))).apply
          (NormalizedVector.ket (R := Qubits (width + 1)) 0) =
        ((queryPipeline width).binaryMatrix (XorOracle.interpretation function)).apply
          (((targetFlip (XorOracle.model width) width).binaryMatrix
            (XorOracle.interpretation function)).apply
            (NormalizedVector.ket (R := Qubits (width + 1)) 0)) := by
    apply NormalizedVector.ext
    intro index
    exact congrArg (fun vector : HilbertVector (Qubits (width + 1)) => vector index)
      (UnitaryOperator.mul_applyVec _ _ _)
  rw [composed, walshNative_targetFlip_apply_zero, walshNative_queryPipeline_apply_input]

end

end QuantumAlg.WalshHadamard.Native
