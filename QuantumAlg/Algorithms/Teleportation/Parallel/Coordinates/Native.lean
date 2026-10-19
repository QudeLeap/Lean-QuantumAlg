/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.NativeMatrices
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Original physical coordinates of the native teleportation bank

The recursive native tensor labels decode to the actual original wires of
each three-system block [dW19, qcnotes.tex:389,790,804]. Both directions of
this coordinate correspondence preserve the original physical triple and
every finite basis value; no subsystem or reference is discarded.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

namespace NativeCoordinates

private lemma wireIndex_zero (count : Nat) (side : Fin 3) :
    wireIndex (0 : Fin (count + 1)) side = Fin.castAdd (width count) side := by
  apply Fin.ext
  change side.val + 3 * 0 = side.val
  omega

private lemma wireIndex_succ (count : Nat) (block : Fin count) (side : Fin 3) :
    wireIndex block.succ side = Fin.natAdd 3 (wireIndex block side) := by
  apply Fin.ext
  change side.val + 3 * (block.val + 1) = 3 + (side.val + 3 * block.val)
  omega

/-- Recursive tensor labels decode to the original physical wire in every triple. -/
lemma bankBinaryBasis_symm_wire (count : Nat) (labels : Fin count → Fin 8)
    (block : Fin count) (side : Fin 3) :
    (BinaryBasis.bigEndianEquiv (width count)).symm
        ((bankBinaryBasis count).symm labels) (wireIndex block side) =
      (BinaryBasis.bigEndianEquiv 3).symm (labels block) side := by
  induction count with
  | zero => exact Fin.elim0 block
  | succ count ih =>
      refine Fin.cases ?_ (fun remaining => ?_) block
      · change (BinaryBasis.bigEndianEquiv (3 + width count)).symm
          (prodEquiv (labels 0,
            (bankBinaryBasis count).symm (fun index => labels index.succ)))
          (wireIndex (0 : Fin (count + 1)) side) = _
        rw [wireIndex_zero]
        exact BinaryBasis.bigEndianEquiv_prod_left _ _ side
      · change (BinaryBasis.bigEndianEquiv (3 + width count)).symm
          (prodEquiv (labels 0,
            (bankBinaryBasis count).symm (fun index => labels index.succ)))
          (wireIndex remaining.succ side) = _
        rw [wireIndex_succ]
        exact (BinaryBasis.bigEndianEquiv_prod_right _ _ (wireIndex remaining side)).trans
          (ih (fun index => labels index.succ) remaining)

/-- Decoding one recursive native label agrees with reading all original wires of that block. -/
lemma tripleBasis_native_decode (count : Nat) (labels : Fin count → Fin 8)
    (block : Fin count) :
    tripleBasis count
        ((BinaryBasis.bigEndianEquiv (width count)).symm
          ((bankBinaryBasis count).symm labels)) block =
      (BinaryBasis.bigEndianEquiv 3).symm (labels block) := by
  funext side
  exact bankBinaryBasis_symm_wire count labels block side

/-- Encoding an arbitrary physical basis does not change any original triple label. -/
lemma bankBinaryBasis_encode (count : Nat) (basis : (layout count).register.Index)
    (block : Fin count) :
    bankBinaryBasis count (BinaryBasis.bigEndianEquiv (width count) basis) block =
      BinaryBasis.bigEndianEquiv 3 (tripleBasis count basis block) := by
  apply (BinaryBasis.bigEndianEquiv 3).symm.injective
  rw [Equiv.symm_apply_apply]
  funext side
  have actual := bankBinaryBasis_symm_wire count
    (bankBinaryBasis count (BinaryBasis.bigEndianEquiv (width count) basis)) block side
  have nativeCancel := congrArg
    (fun label : Fin (2 ^ width count) =>
      (BinaryBasis.bigEndianEquiv (width count)).symm label (wireIndex block side))
    ((bankBinaryBasis count).symm_apply_apply
      (BinaryBasis.bigEndianEquiv (width count) basis))
  have binaryCancel := congrFun
    ((BinaryBasis.bigEndianEquiv (width count)).symm_apply_apply basis) (wireIndex block side)
  exact actual.symm.trans (nativeCancel.trans binaryCancel)

end NativeCoordinates

end

end QuantumAlg.QuantumTeleportation.Parallel
