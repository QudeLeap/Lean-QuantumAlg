/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Recompute

/-!
# Complete actual division branch after measurement reset

The actual native product has saved X-inverse times old Y in A. Its H/Z
measurement and selected reset supply the complete frame with Y=0 and
the original Y Walsh character. The same reused EEA backward, actual
selected recomputation correction and literal A/Y swap return the quotient
in Y while restoring X and every fixed auxiliary bit
[LYL+26, sec_point_add/sec_point_add.tex:67-105].

This is the flat-vector action of those existing native programs. It does
not replace the runtime H/Z/classical-store proof or add a new interpreter.
The canonical original numerator may be zero throughout.
-/

namespace QuantumAlg.MeasuredUncompute.DivisionBranch

noncomputable section

open ProductPlacement MAU.Inversion.SharedEEA InPlaceArithmetic

/-- The exact post-reset native sequence cancels the measured character and restores the seed. -/
theorem after_reset (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator outcome : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    let completed := InPlaceForward.result modulus value.val positive bounded
    let multiplied := NativeProductFrame.step modulus.size (modulusWord modulus)
      (completed, numerator)
    ((NativeEEAFrame.backward modulus prime).seq
      ((ReusedProduct.correction modulus.size (modulusWord modulus)
        (fun index => outcome.val.testBit index.val)).seq
          (FrameSwap.program modulus.size))).applyVec
        (WalshHadamard.walshSign outcome numerator •
          (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
            ((frameEncoding modulus.size).encode (multiplied.1, 0))).vec) =
      (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (InitialPortProgram.inputFrame modulus value,
            InPlaceRecompute.saved modulus value numerator positive bounded))).vec := by
  dsimp only
  rw [UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_smul]
  have backward := congrArg
    (fun state : NormalizedVector (Qubits (frameEncoding modulus.size).width) => state.vec)
    (backward_reset_ket modulus prime value numerator positive bounded)
  change (NativeEEAFrame.backward modulus prime).applyVec
    (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
      ((frameEncoding modulus.size).encode
        ((NativeProductFrame.step modulus.size (modulusWord modulus)
          (InPlaceForward.result modulus value.val positive bounded, numerator)).1, 0))).vec =
    (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
      ((frameEncoding modulus.size).encode
        (InPlaceRecompute.recovered modulus value numerator positive bounded))).vec at backward
  rw [backward]
  exact InPlaceRecompute.correction_swap modulus prime value numerator outcome
    positive bounded numeratorBound

end

end QuantumAlg.MeasuredUncompute.DivisionBranch
