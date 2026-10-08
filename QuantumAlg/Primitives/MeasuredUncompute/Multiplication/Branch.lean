/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Multiplication.Recompute

/-!
# Complete actual multiplication branch after measurement reset

The H/Z/reset interpreter supplies a branch with the original Y Walsh
character on the complete reset product frame. The exact remaining gate
sequence is reused EEA forward, selected product phase correction, the
identical reused EEA backward, and the literal A/Y swap. This theorem
composes those actual operators without replacing a label or discarding
Γ [LYL+26, sec_point_add/sec_point_add.tex:119-122].

The measured branch's normalization factor and external correlations are
handled by the existing linear execution semantics, not by an additional
measurement model in this module.
-/

namespace QuantumAlg.MeasuredUncompute.MultiplicationBranch

noncomputable section

open ProductPlacement MAU.Inversion.SharedEEA
open InPlaceArithmetic MultiplicationArithmetic

/-- The exact post-reset native gate sequence cancels the old Y phase and outputs X*Y. -/
theorem after_reset (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    ((NativeReusedEEA.forward modulus prime).seq
      ((ReusedProduct.correction modulus.size (modulusWord modulus)
        (fun index => outcome.val.testBit index.val)).seq
          ((NativeEEAFrame.backward modulus prime).seq (FrameSwap.program modulus.size)))).applyVec
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (resetFrame modulus value numerator)))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
          (InitialPortProgram.inputFrame modulus value, saved modulus value numerator)))).vec := by
  rw [UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_smul]
  have forward := congrArg
    (fun state :
      NormalizedVector (QubitLayout.canonical (frameEncoding modulus.size).width).toQuantum.register
      => state.vec)
    (forward_ket modulus prime value numerator positive bounded)
  change (NativeReusedEEA.forward modulus prime).applyVec
    (NormalizedVector.ket
      ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode
      (resetFrame modulus value numerator)))).vec = _ at forward
  rw [forward]
  exact MultiplicationRecompute.correction_backward_swap modulus prime value numerator outcome
    positive bounded numeratorBound

end

end QuantumAlg.MeasuredUncompute.MultiplicationBranch
