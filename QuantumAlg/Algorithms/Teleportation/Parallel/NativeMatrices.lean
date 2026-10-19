/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.NativeMatrices
import all QuantumAlg.Algorithms.Teleportation.Mathematics
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Full native bank operators in their original block coordinates

The consecutive parallel constructor determines both native words' actual
matrices. Recursively splitting the canonical big-endian register identifies
their tensor entries, including every off-diagonal pair of block labels
[dW19, qcnotes.tex:389,790,804]. No product-state assumption is made.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open scoped BigOperators

/-- Split consecutive canonical triples using the same big-endian tensor convention. -/
def bankBinaryBasis : (count : Nat) → (Qubits (width count)).Index ≃ (Fin count → Fin 8)
  | 0 =>
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim (α := Fin 1) _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | count + 1 =>
      ((prodEquiv (m := 3) (n := width count)).symm.trans
        ((Equiv.refl (Fin 8)).prodCongr (bankBinaryBasis count))).trans
        (Fin.consEquiv (fun _ : Fin (count + 1) => Fin 8))

/-- Mathematical tensor of the one-block operators, used to observe an already built word. -/
def operatorBank : (count : Nat) → (Fin count → UnitaryOperator (Qubits 3)) →
    UnitaryOperator (Qubits (width count))
  | 0, _ => 1
  | count + 1, operators =>
      (operators 0).tensor (operatorBank count (fun index => operators index.succ))

/-- Every tensor entry includes all block coherences, including arbitrary different columns. -/
lemma operatorBank_entry (count : Nat) (operators : Fin count → UnitaryOperator (Qubits 3))
    (row column : Fin count → Fin 8) :
    operatorBank count operators ((bankBinaryBasis count).symm row)
      ((bankBinaryBasis count).symm column) =
        ∏ index : Fin count, operators index (row index) (column index) := by
  induction count with
  | zero =>
      simp only [Fin.prod_univ_zero]
      change (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1
      exact Matrix.one_apply_eq 0
  | succ count ih =>
      change ((operators 0).tensor
        (operatorBank count (fun index => operators index.succ)))
          (prodEquiv (row 0, (bankBinaryBasis count).symm (fun index => row index.succ)))
          (prodEquiv (column 0, (bankBinaryBasis count).symm
            (fun index => column index.succ))) = _
      rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        ih, Fin.prod_univ_succ]

/-- Alice's actual bank word realizes the tensor of the source's original CNOT/H operators. -/
lemma aliceWord_binaryMatrix (count : Nat) (environment : OracleModel.empty.Interpretation) :
    ((aliceWord count).binaryMatrix environment)
      = operatorBank count (fun _ => teleportBellMeasure) := by
  induction count with
  | zero => exact UnitaryCircuit.unitaryCircuit_binaryMatrix_identity _ _ 0 environment
  | succ count ih =>
      exact (UnitaryCircuit.parallelBinary_binaryMatrix Block.aliceWord (aliceWord count)
        environment).trans
        (congrArg₂ (fun first : UnitaryOperator (Qubits 3) =>
          fun second : UnitaryOperator (Qubits (width count)) => first.tensor second)
          (Block.teleportation_aliceWord_binaryMatrix environment) ih)

/-- The actual selected correction bank acts on Bob's original qubit in every triple. -/
lemma correctionWord_binaryMatrix (count : Nat) (bits : Fin count → Bool × Bool)
    (environment : OracleModel.empty.Interpretation) :
    ((correctionWord count bits).binaryMatrix environment) =
      operatorBank count (fun index =>
        (1 : UnitaryOperator (Qubits 2)).tensor
          (teleportCorrection (bits index).1 (bits index).2)) := by
  induction count with
  | zero => exact UnitaryCircuit.unitaryCircuit_binaryMatrix_identity _ _ 0 environment
  | succ count ih =>
      exact (UnitaryCircuit.parallelBinary_binaryMatrix
        (Block.correctionWord (bits 0).1 (bits 0).2)
        (correctionWord count (fun index => bits index.succ)) environment).trans
          (congrArg₂ (fun first : UnitaryOperator (Qubits 3) =>
            fun second : UnitaryOperator (Qubits (width count)) => first.tensor second)
            (Block.teleportation_correctionWord_binaryMatrix (bits 0).1 (bits 0).2 environment)
            (ih _))

end

end QuantumAlg.QuantumTeleportation.Parallel
