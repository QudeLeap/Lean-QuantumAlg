/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Correction
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap
import all QuantumAlg.Core.Execution.Output

/-!
# The single actual circuit for in-place measured division

The two supplied words are X and Y. One fixed preparation supplies A=0
and the original small EEA seed; retaining the measurement cells adds no
quantum system. The actual instruction order is forward EEA, native
product into A, H/Z/store/read/reset on Y, the same EEA adjoint using Y,
stored-result product phase correction, then the literal A/Y swap
[LYL+26, sec_point_add/sec_point_add.tex:45-105].

All native members use the same proved runtime wire assembly beside the
retained cells. Every live quantum bank and classical result is listed in
the output. The finite result read selects the existing correction body;
it is not a separately invented arithmetic event or hidden packed cell.
Semantic correctness is proved separately for this exact circuit.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceDivision

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Execute the complete existing forward EEA on X/A, retaining Y and all real result cells. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size (NativeEEAFrame.forward modulus prime)

/-- The actual product uses X/Y/A in the same original frame, without another output bank. -/
def product (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size
    (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))

/-- Execute the identical EEA adjoint on its actually reused Y workspace. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  NumeratorRuntime.code modulus.size (NativeEEAFrame.backward modulus prime)

/-- The final native three-CNOT-per-bit swap acts on the original A and Y physical ports. -/
def swap (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  NumeratorRuntime.code width (FrameSwap.program width)

/-- All six actual execution blocks retain their exact source order and the same full context. -/
def body (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size) :=
  .seq (forward modulus prime)
    (.seq (product modulus)
      (.seq (NumeratorReset.code modulus.size)
        (.seq (backward modulus prime)
          (.seq (NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus))
            (swap modulus.size)))))

/-- Actual fixed allocation, actual finite cells, then the single measured arithmetic circuit. -/
def code (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (InversePreparation.before modulus.size) (NumeratorMeasurement.context modulus.size) :=
  .seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime))

/-- List every live key and read precisely the finite outcomes retained by the actual Z writes. -/
def output (width : Nat) :
    Output (NumeratorMeasurement.context width) (.fixedVector width (.finite 2)) :=
  Output.all (NumeratorMeasurement.context width) (.read (NumeratorMeasurement.input width))

/-- The output contains every live bank and measurement cell, without omitting auxiliary state. -/
lemma output_listing (width : Nat) :
    (output width).listing = (NumeratorMeasurement.context width).keys :=
  Output.all_listing _ _

/-- The classical result is the actual structural read of the cells written by measurement. -/
lemma output_read (width : Nat) (store : Store (NumeratorMeasurement.context width)) :
    (output width).eval store = store.read (NumeratorMeasurement.input width) :=
  Output.all_eval _ _ _

/-- The only extra quantum bank is the original shared-frame complement prepared beside X/Y. -/
lemma final_physical (width : Nat) :
    (NumeratorMeasurement.context width).physicalIdx =
      (InversePreparation.after width).physicalIdx :=
  NumeratorMeasurement.context_physical width

end

end QuantumAlg.MeasuredUncompute.InPlaceDivision
