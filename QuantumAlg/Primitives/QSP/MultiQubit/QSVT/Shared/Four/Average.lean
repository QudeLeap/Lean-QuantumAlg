/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator

/-!
# Three-ancilla coherent averaging in original binary coordinates

The two selectors average four branches, while the phase ancilla extracts
each branch's plus-state block. All relative phases remain in those blocks.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

/-- The intrinsic selector average, without changing the original binary coordinate order. -/
def binaryAverage {width : Nat} (A B : UnitaryOperator (Qubits width)) :
    UnitaryOperator (Qubits (1 + width)) :=
  phaseHadamardWrapperOperator (phaseControlledDirectSumOperator A B)

private lemma binaryAverage_block {width : Nat} (A B : UnitaryOperator (Qubits width)) :
    ancillaBlock 0 0 (binaryAverage A B : HilbertOperator (Qubits (1 + width))) =
      (1 / 2 : ℂ) • (A : HilbertOperator (Qubits width)) +
        (1 / 2 : ℂ) • (B : HilbertOperator (Qubits width)) := by
  change projectedBlock 1 width (phaseHadamardWrapperOperator
    (phaseControlledDirectSumOperator A B)) = _
  rw [projectedBlock_phaseHadamardWrapper, phasePlusBlock_phaseControlledDirectSum]

private lemma ancillaBlock_add {width : Nat} (a b : Fin 2)
    (A B : HilbertOperator (Qubits (1 + width))) :
    ancillaBlock a b (A + B) = ancillaBlock a b A + ancillaBlock a b B := rfl

private lemma ancillaBlock_smul {width : Nat} (a b : Fin 2) (scalar : ℂ)
    (A : HilbertOperator (Qubits (1 + width))) :
    ancillaBlock a b (scalar • A) = scalar • ancillaBlock a b A := rfl

private lemma hadamard_block {width : Nat} (A : UnitaryOperator (Qubits (1 + width))) :
    ancillaBlock 0 0 (phaseHadamardWrapperOperator A :
      HilbertOperator (Qubits (1 + width))) = phasePlusBlock A :=
  projectedBlock_phaseHadamardWrapper A

/-- Four source branches with two selector averages and one common phase-ancilla projection. -/
def threeAverage {width : Nat} (A B C D : UnitaryOperator (Qubits (1 + width))) :
    UnitaryOperator (Qubits (1 + (1 + (1 + width)))) :=
  binaryAverage
    (binaryAverage (phaseHadamardWrapperOperator A) (phaseHadamardWrapperOperator B))
    (binaryAverage (phaseHadamardWrapperOperator C) (phaseHadamardWrapperOperator D))

/-- The exact zero block of all three ancillas is one quarter of the four original plus blocks. -/
lemma threeAverage_zero_block {width : Nat}
    (A B C D : UnitaryOperator (Qubits (1 + width))) :
    ancillaBlock 0 0 (ancillaBlock 0 0 (ancillaBlock 0 0
      (threeAverage A B C D : HilbertOperator (Qubits (1 + (1 + (1 + width))))))) =
      (1 / 4 : ℂ) • phasePlusBlock A + (1 / 4 : ℂ) • phasePlusBlock B +
        ((1 / 4 : ℂ) • phasePlusBlock C + (1 / 4 : ℂ) • phasePlusBlock D) := by
  rw [threeAverage, binaryAverage_block]
  repeat rw [ancillaBlock_add]
  repeat rw [ancillaBlock_smul]
  rw [binaryAverage_block, binaryAverage_block]
  repeat rw [ancillaBlock_add]
  repeat rw [ancillaBlock_smul]
  repeat rw [hadamard_block]
  simp only [smul_add, smul_smul]
  norm_num

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
