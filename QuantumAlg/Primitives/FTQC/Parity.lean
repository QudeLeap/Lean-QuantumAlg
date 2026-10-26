/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.FTQC.Toffoli7T.Base
import all QuantumAlg.Util.Matrix.WeightedPermutation
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Components.Gates.Toffoli.Semantics

/-!
# Sparse phase-polynomial multiplication on the original three bits

Diagonal phases and actual CNOT permutations compose before any matrix
entry is expanded. The already proved native Toffoli identity supplies
the common two-Hadamard boundary without another finite matrix product.
-/

namespace QuantumAlg.FTQC.Parity

open CliffordT Gate UnitaryCircuit

noncomputable section

/-- The original all-one phase in big-endian binary coordinates. -/
def cczMatrix : HilbertOperator (Qubits 3) :=
  Matrix.diagonal (fun label => if label = (7 : Fin 8) then -1 else 1)

lemma diagonal_weighted {Index R : Type*} [DecidableEq Index] [Semiring R]
    (values : Index → R) :
    Matrix.diagonal values = WeightedPermutation.matrix values (Equiv.refl _) :=
  (WeightedPermutation.refl_eq_diagonal values).symm

lemma cnot_weighted (control target : Fin 3) (different : control ≠ target) :
    (QubitPrimitive.operator (.cnot control target different) : HilbertOperator (Qubits 3)) =
      WeightedPermutation.matrix (fun _ => 1)
        (QubitPrimitive.perm (.cnot control target different)).symm := by
  ext row column
  exact UnitaryOperator.ofPerm_entry _ row column

lemma cnot01_apply (different : (0 : Fin 3) ≠ 1) (label : Fin 8) :
    (QubitPrimitive.perm (.cnot 0 1 different)).symm label =
      (![0, 1, 2, 3, 6, 7, 4, 5] : Fin 8 → Fin 8) label := by
  change (QubitPrimitive.perm (.cnot (0 : Fin 3) 1 (by decide))).symm label =
    (![0, 1, 2, 3, 6, 7, 4, 5] : Fin 8 → Fin 8) label
  fin_cases label <;> decide +kernel

lemma cnot02_apply (different : (0 : Fin 3) ≠ 2) (label : Fin 8) :
    (QubitPrimitive.perm (.cnot 0 2 different)).symm label =
      (![0, 1, 2, 3, 5, 4, 7, 6] : Fin 8 → Fin 8) label := by
  change (QubitPrimitive.perm (.cnot (0 : Fin 3) 2 (by decide))).symm label =
    (![0, 1, 2, 3, 5, 4, 7, 6] : Fin 8 → Fin 8) label
  fin_cases label <;> decide +kernel

lemma cnot10_apply (different : (1 : Fin 3) ≠ 0) (label : Fin 8) :
    (QubitPrimitive.perm (.cnot 1 0 different)).symm label =
      (![0, 1, 6, 7, 4, 5, 2, 3] : Fin 8 → Fin 8) label := by
  change (QubitPrimitive.perm (.cnot (1 : Fin 3) 0 (by decide))).symm label =
    (![0, 1, 6, 7, 4, 5, 2, 3] : Fin 8 → Fin 8) label
  fin_cases label <;> decide +kernel

lemma cnot20_apply (different : (2 : Fin 3) ≠ 0) (label : Fin 8) :
    (QubitPrimitive.perm (.cnot 2 0 different)).symm label =
      (![0, 5, 2, 7, 4, 1, 6, 3] : Fin 8 → Fin 8) label := by
  change (QubitPrimitive.perm (.cnot (2 : Fin 3) 0 (by decide))).symm label =
    (![0, 5, 2, 7, 4, 1, 6, 3] : Fin 8 → Fin 8) label
  fin_cases label <;> decide +kernel

lemma cnot12_apply (different : (1 : Fin 3) ≠ 2) (label : Fin 8) :
    (QubitPrimitive.perm (.cnot 1 2 different)).symm label =
      (![0, 1, 3, 2, 4, 5, 7, 6] : Fin 8 → Fin 8) label := by
  change (QubitPrimitive.perm (.cnot (1 : Fin 3) 2 (by decide))).symm label =
    (![0, 1, 3, 2, 4, 5, 7, 6] : Fin 8 → Fin 8) label
  fin_cases label <;> decide +kernel

private lemma toffoli_swap :
    toffoliOp = UnitaryOperator.ofPerm (R := Qubits 3) (Equiv.swap (6 : Fin 8) 7) := by
  unfold toffoliOp QubitPrimitive.operator
  apply congrArg (UnitaryOperator.ofPerm (R := Qubits 3))
  ext label
  fin_cases label <;> decide +kernel

/-- The exact established native Toffoli identity factors the common target Hadamards. -/
lemma hadamard_conjugate_ccz (oracles : OracleModel) (environment : oracles.Interpretation) :
    HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
        (HOp : HilbertOperator (Qubits 1)) *
      (cczMatrix * HilbertOperator.tensor (1 : HilbertOperator (Qubits 2))
        (HOp : HilbertOperator (Qubits 1))) =
      (toffoliOp : HilbertOperator (Qubits 3)) := by
  have original := Gate.Toffoli.toffoliExpansion_binaryMatrix oracles environment
  rw [Gate.Toffoli.circuit, unitaryCircuit_binaryMatrix_seq,
    unitaryCircuit_binaryMatrix_seq, Gate.Toffoli.toffoliExpansion_hadamard_binary] at original
  have coefficients := congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    (operator : HilbertOperator (Qubits 3))) original
  change HilbertOperator.tensor 1 (HOp : HilbertOperator (Qubits 1)) *
    (_ * HilbertOperator.tensor 1 (HOp : HilbertOperator (Qubits 1))) = _ at coefficients
  rw [Gate.Toffoli.toffoliExpansion_phaseWord_binary] at coefficients
  exact coefficients.trans (congrArg
    (fun operator : UnitaryOperator (Qubits 3) =>
      (operator : HilbertOperator (Qubits 3))) toffoli_swap).symm

end

end QuantumAlg.FTQC.Parity
