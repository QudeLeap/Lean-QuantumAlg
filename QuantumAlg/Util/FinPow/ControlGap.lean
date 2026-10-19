/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow

/-!
# Moving one binary coordinate before a finite gap

This equivalence changes the order of the gap and one distinguished bit while
preserving every value, including empty gap and source segments. It is only
index plumbing: physical placement and native execution require their own
certified embeddings.
-/

namespace QuantumAlg.BinaryBasis

/-- Exchange a gap and one distinguished bit in a nested big-endian label. -/
public def controlGapEquiv (gap width : Nat) :
    Fin (2 ^ (gap + (1 + width))) ≃ Fin (2 ^ (1 + (gap + width))) :=
  (prodEquiv (m := gap) (n := 1 + width)).symm |>.trans
    (Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := 1) (n := width)).symm) |>.trans
    (Equiv.prodAssoc (Fin (2 ^ gap)) (Fin 2) (Fin (2 ^ width))).symm |>.trans
    (Equiv.prodCongr (Equiv.prodComm (Fin (2 ^ gap)) (Fin 2)) (Equiv.refl _)) |>.trans
    (Equiv.prodAssoc (Fin 2) (Fin (2 ^ gap)) (Fin (2 ^ width))) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := gap) (n := width))) |>.trans
    (prodEquiv (m := 1) (n := gap + width))

/-- The gap, distinguished bit, and source values are retained exactly. -/
public lemma controlGapEquiv_apply {gap width : Nat}
    (before : Fin (2 ^ gap)) (control : Fin 2) (source : Fin (2 ^ width)) :
    controlGapEquiv gap width (prodEquiv (before, prodEquiv (control, source))) =
      prodEquiv (control, prodEquiv (before, source)) := by
  simp [controlGapEquiv]

/-- The inverse also retains all three original coordinate values. -/
public lemma controlGapEquiv_symm_apply {gap width : Nat}
    (before : Fin (2 ^ gap)) (control : Fin 2) (source : Fin (2 ^ width)) :
    (controlGapEquiv gap width).symm (prodEquiv (control, prodEquiv (before, source))) =
      prodEquiv (before, prodEquiv (control, source)) := by
  exact (Equiv.symm_apply_eq (controlGapEquiv gap width)).mpr
    (controlGapEquiv_apply before control source).symm

end QuantumAlg.BinaryBasis
