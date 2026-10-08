/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Quantum
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact basis coordinates for appended quantum layouts

Splitting an appended basis label uses the actual left and right wire positions.
Reassembly uses those same positions and their proved dimensions, rather than a
bijection obtained only from the cardinalities of the Hilbert spaces. This is
the concrete layout realization of the tensor basis [dW19, qcnotes.tex:389].
-/

section

namespace QuantumAlg.QuantumLayout

variable {leftCount rightCount : Nat}

/-- Restrict a joint label to the exact left wire positions. -/
@[expose]
public def appendLeftBasis (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (basis : (append left right disjoint).Basis) : left.Basis :=
  fun index => Fin.cast (by simp [append]) (basis (Fin.castAdd rightCount index))

/-- Restrict a joint label to the exact right wire positions. -/
@[expose]
public def appendRightBasis (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (basis : (append left right disjoint).Basis) : right.Basis :=
  fun index => Fin.cast (by simp [append]) (basis (Fin.natAdd leftCount index))

/-- Reassemble labels using the two actual segments of the appended layout. -/
@[expose]
public def appendJoinBasis (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (leftBasis : left.Basis) (rightBasis : right.Basis) :
    (append left right disjoint).Basis :=
  Fin.addCases
    (fun index => Fin.cast (by simp [append]) (leftBasis index))
    (fun index => Fin.cast (by simp [append]) (rightBasis index))

/-- Exact tensor-basis equivalence certified by the wirewise inverse laws. -/
@[expose]
public def appendBasisEquiv (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    (append left right disjoint).Basis ≃ left.Basis × right.Basis where
  toFun basis :=
    (appendLeftBasis left right disjoint basis, appendRightBasis left right disjoint basis)
  invFun basis := appendJoinBasis left right disjoint basis.1 basis.2
  left_inv basis := by
    funext index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · apply Fin.ext
      simp [appendJoinBasis, appendLeftBasis]
    · apply Fin.ext
      simp [appendJoinBasis, appendRightBasis]
  right_inv basis := by
    apply Prod.ext
    · funext index
      apply Fin.ext
      simp [appendLeftBasis, appendJoinBasis]
    · funext index
      apply Fin.ext
      simp [appendRightBasis, appendJoinBasis]

/-- Splitting reassembled labels recovers both original labels exactly. -/
public theorem appendBasisEquiv_join (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (leftBasis : left.Basis) (rightBasis : right.Basis) :
    appendBasisEquiv left right disjoint
      (appendJoinBasis left right disjoint leftBasis rightBasis) = (leftBasis, rightBasis) :=
  (appendBasisEquiv left right disjoint).apply_symm_apply (leftBasis, rightBasis)

/-- Joining the two all-zero subsystem labels gives the all-zero label of the
complete appended layout. -/
public theorem appendJoinBasis_zero (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    appendJoinBasis left right disjoint left.zeroLabel right.zeroLabel =
      (append left right disjoint).zeroLabel := by
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · apply Fin.ext
    simp [appendJoinBasis, zeroLabel]
  · apply Fin.ext
    simp [appendJoinBasis, zeroLabel]

/-- The left physical wire receives precisely its original finite value. -/
public theorem appendJoinBasis_left_value (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (leftBasis : left.Basis) (rightBasis : right.Basis) (index : Fin leftCount) :
    (appendJoinBasis left right disjoint leftBasis rightBasis
      (Fin.castAdd rightCount index)).val = (leftBasis index).val := by
  simp [appendJoinBasis]

/-- The right physical wire receives precisely its original finite value. -/
public theorem appendJoinBasis_right_value (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (leftBasis : left.Basis) (rightBasis : right.Basis) (index : Fin rightCount) :
    (appendJoinBasis left right disjoint leftBasis rightBasis
      (Fin.natAdd leftCount index)).val = (rightBasis index).val := by
  simp [appendJoinBasis]

end QuantumAlg.QuantumLayout

end
