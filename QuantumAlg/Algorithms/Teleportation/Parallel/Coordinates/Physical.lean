/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Native
import all QuantumAlg.Algorithms.Teleportation.Parallel.NativeMatrices
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Actual teleportation operators in original physical coordinates

Equality of the complete physical wire records transports the native tensor
labels to the live context without changing any basis value [dW19,
qcnotes.tex:389,790,804]. Alice's actual word and Bob's correction selected by
the stored bits then have the corresponding block matrix entries. Both row
and column labels are arbitrary; no product-state assumption is imposed.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.PhysicalNative

noncomputable section

open Execution NativeCoordinates
open scoped BigOperators

/-- The native tensor labels are transported through equality of complete physical wire records. -/
def contextBankBasis (count : Nat) :
    (context count).register.Index ≃ (Fin count → Fin 8) :=
  (basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)).symm.trans
      ((QuantumSignature.qubitsIndexEquiv (width count)).trans (bankBinaryBasis count))

/-- Decoding a tensor block preserves the value on its actual original physical system. -/
lemma contextBankBasis_symm_wire_value (count : Nat) (labels : Fin count → Fin 8)
    (block : Fin count) (side : Fin 3) :
    (((contextBankBasis count).symm labels)
      (position count (wireIndex block side))).val =
        ((BinaryBasis.bigEndianEquiv 3).symm (labels block) side).val :=
  (basisOfEqualWires_value (layout count) (context count).quantumLayout
    (context_wires count)
    ((BinaryBasis.bigEndianEquiv (width count)).symm ((bankBinaryBasis count).symm labels))
    (wireIndex block side)).trans
      (congrArg Fin.val (bankBinaryBasis_symm_wire count labels block side))

/-- Equal-wire placement and native integer labels commute on both arbitrary matrix coordinates. -/
lemma onContext_native_entry (count : Nat)
    (word : UnitaryCircuit AlgorithmGate.model .empty (layout count))
    (row column : Fin count → Fin 8) (environment : OracleModel.empty.Interpretation) :
    ((onContext count word).matrix environment) ((contextBankBasis count).symm row)
      ((contextBankBasis count).symm column) =
      (word.binaryMatrix environment) ((bankBinaryBasis count).symm row)
        ((bankBinaryBasis count).symm column) := by
  let physical := basisOfEqualWires (layout count) (context count).quantumLayout
    (context_wires count)
  let left := (QuantumSignature.qubitsIndexEquiv (width count)).symm
    ((bankBinaryBasis count).symm row)
  let right := (QuantumSignature.qubitsIndexEquiv (width count)).symm
    ((bankBinaryBasis count).symm column)
  have moved := congrArg (fun operator : UnitaryOperator (context count).register =>
    operator ((contextBankBasis count).symm row) ((contextBankBasis count).symm column))
      (unitaryOfEqualWires_matrix (layout count) (context count).quantumLayout
        (context_wires count) environment word)
  refine moved.trans ?_
  change ((word.matrix environment) : HilbertOperator (layout count).register)
      (physical.symm (physical left)) (physical.symm (physical right)) =
    ((word.matrix environment) : HilbertOperator (layout count).register) left right
  exact congrArg₂ (fun first second : (layout count).register.Index =>
    ((word.matrix environment) : HilbertOperator (layout count).register) first second)
      (physical.symm_apply_apply left) (physical.symm_apply_apply right)

/-- The full actual Alice matrix factors by physical triples, not by an input-state assumption. -/
lemma alice_matrix_entry (count : Nat) (row column : Fin count → Fin 8)
    (environment : OracleModel.empty.Interpretation) :
    ((onContext count (aliceWord count)).matrix environment) ((contextBankBasis count).symm row)
      ((contextBankBasis count).symm column) =
        ∏ block : Fin count, teleportBellMeasure (row block) (column block) :=
  (onContext_native_entry count (aliceWord count) row column environment).trans
    ((congrArg (fun operator : UnitaryOperator (Qubits (width count)) =>
      operator ((bankBinaryBasis count).symm row) ((bankBinaryBasis count).symm column))
        (aliceWord_binaryMatrix count environment)).trans
      (operatorBank_entry count (fun _ => teleportBellMeasure) row column))

/-- Actual feedback selects the source correction on each original Bob system. -/
lemma correction_matrix_entry (count : Nat) (value : CShape.Value (resultShape count))
    (row column : Fin count → Fin 8) (environment : OracleModel.empty.Interpretation) :
    ((selectedCorrection count value).matrix environment) ((contextBankBasis count).symm row)
      ((contextBankBasis count).symm column) =
        ∏ block : Fin count,
          ((1 : UnitaryOperator (Qubits 2)).tensor
            (teleportCorrection (storedBits value block).1 (storedBits value block).2))
              (row block) (column block) :=
  (onContext_native_entry count (correctionWord count (storedBits value)) row column
    environment).trans
    ((congrArg (fun operator : UnitaryOperator (Qubits (width count)) =>
      operator ((bankBinaryBasis count).symm row) ((bankBinaryBasis count).symm column))
        (correctionWord_binaryMatrix count (storedBits value) environment)).trans
      (operatorBank_entry count (fun block =>
        (1 : UnitaryOperator (Qubits 2)).tensor
          (teleportCorrection (storedBits value block).1 (storedBits value block).2)) row column))

end

end QuantumAlg.QuantumTeleportation.Parallel.PhysicalNative
