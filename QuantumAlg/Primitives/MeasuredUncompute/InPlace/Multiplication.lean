/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic
import all QuantumAlg.Primitives.MeasuredUncompute.Native.ReusedEEA
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Correction
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap
import all QuantumAlg.Core.Execution.Output

/-!
# The single actual circuit for in-place measured multiplication

First save X*Y in A, then apply the actual H/Z/store/read/reset sequence to
Y. The reset word supplies the large workspace for forward EEA on the
original nonzero denominator X. Stored outcomes select recomputation of
X-inverse times saved A, its Z correction and identical product adjoint.
The same reused EEA backward restores X and Γ, and the literal final swap
places X*Y in Y [LYL+26, sec_point_add/sec_point_add.tex:32-36,119-122].

Y and the saved product may be zero. No inverse of Y, slope or product is
used. The preparation, physical frame, retained finite result cells and
complete output are the existing two-input shared-EEA ones.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceMultiplication

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Save the actual X/Y product in the clean original A port before measuring Y. -/
def product (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size
    (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))

/-- Invert only original X, using the actually reset Y as its large workspace. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size (NativeReusedEEA.forward modulus prime)

/-- Restore the original X and complete fixed Γ using the same reused EEA backward program. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size (NativeEEAFrame.backward modulus prime)

/-- Execute the actual final A/Y exchange with all other live systems retained. -/
def swap (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  NumeratorRuntime.code width (FrameSwap.program width)

/-- The exact multiplication schedule uses measured Y before its workspace-reuse EEA passes. -/
def body (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  .seq (product modulus)
    (.seq (NumeratorReset.code modulus.size)
      (.seq (forward modulus prime)
        (.seq (NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus))
          (.seq (backward modulus prime) (swap modulus.size)))))

/-- Fixed A=0 and Γ preparation, actual finite-cell allocation, then the actual multiplication. -/
def code (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (InversePreparation.before modulus.size) (NumeratorMeasurement.context modulus.size) :=
  .seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime))

/-- Retain every live bank and cell, and read exactly the actually written finite outcomes. -/
def output (width : Nat) :
    Output (NumeratorMeasurement.context width) (.fixedVector width (.finite 2)) :=
  Output.all (NumeratorMeasurement.context width) (.read (NumeratorMeasurement.input width))

lemma output_listing (width : Nat) :
    (output width).listing = (NumeratorMeasurement.context width).keys :=
  Output.all_listing _ _

lemma output_read (width : Nat) (store : Store (NumeratorMeasurement.context width)) :
    (output width).eval store = store.read (NumeratorMeasurement.input width) :=
  Output.all_eval _ _ _

end

end QuantumAlg.MeasuredUncompute.InPlaceMultiplication
