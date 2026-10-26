/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Ring
public import QuantumAlg.Util.CliffordT.Packed

/-!
# Packed evaluation of Clifford+T words

A left fold keeps the intermediate matrix in four entries. Its exact equality
with `evalRing` preserves the word semantics and the first-letter-first order.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

namespace Letter

/-- Apply a letter to a packed accumulated matrix. -/
def applyPacked (a : Letter) (m : PackedMat2) : PackedMat2 :=
  match a with
  | .h => m.stepH
  | .s => m.stepS
  | .t => m.stepT

lemma toMatrix_applyPacked (a : Letter) (m : PackedMat2) :
    (a.applyPacked m).toMatrix = a.ringMatrix * m.toMatrix := by
  cases a
  · exact PackedMat2.toMatrix_stepH m
  · exact PackedMat2.toMatrix_stepS m
  · exact PackedMat2.toMatrix_stepT m

end Letter

private lemma packed_fold_matrix (w : List Letter) (m : PackedMat2) :
    (w.foldl (fun acc a => a.applyPacked acc) m).toMatrix = evalRing w * m.toMatrix := by
  induction w generalizing m with
  | nil => exact (one_mul m.toMatrix).symm
  | cons a w ih =>
      change (w.foldl (fun acc a => a.applyPacked acc) (a.applyPacked m)).toMatrix =
        (evalRing w * a.ringMatrix) * m.toMatrix
      rw [ih, Letter.toMatrix_applyPacked, mul_assoc]

/-- Kernel-friendly exact word evaluation, equal to `evalRing`. -/
def evalRingPacked (w : List Letter) : Mat2 :=
  (w.foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix

lemma evalRingPacked_eq_evalRing (w : List Letter) : evalRingPacked w = evalRing w := by
  simp [evalRingPacked, packed_fold_matrix, PackedMat2.toMatrix_identity]

end QuantumAlg.CliffordT
