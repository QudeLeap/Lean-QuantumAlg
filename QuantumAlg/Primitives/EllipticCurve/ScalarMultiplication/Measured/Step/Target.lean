/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates

/-!
# Exact permutation of the complete measured scalar workspace

The independent indexed target applies the original point permutation on its
actual selected coordinates. All ambient systems and the external reference
retain their original values. This equality holds on every basis value; the
domain on which the measured circuit realizes it remains a separate condition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The full independent step permutes the selected point and retains every ambient system. -/
def stepPermutation {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    Equiv.Perm (readyContext p.size count).register.Index :=
  (pointBasis p.size active).trans
    ((Equiv.prodCongr (MeasuredPointAddition.targetPermutation E Q) (Equiv.refl _)).trans
      (pointBasis p.size active).symm)

/-- The independent step changes exactly the original point coordinate of the complete basis. -/
lemma pointBasis_stepPermutation {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    pointBasis p.size active (stepPermutation E Q active value) =
      (MeasuredPointAddition.targetPermutation E Q (pointBasis p.size active value).1,
        (pointBasis p.size active value).2) := by
  simp only [stepPermutation, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]

private lemma originalTarget_apply_ket {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference : Register}
    (value : (MeasuredPointAddition.context p.size).register.Index)
    (reference : Reference.Index) :
    (MeasuredPointAddition.target E Q Reference).applyVec
      (NormalizedVector.ket (value, reference)).vec =
        (NormalizedVector.ket
          (MeasuredPointAddition.targetPermutation E Q value, reference)).vec := by
  apply MeasuredPointAddition.operator_prodTensor_identity_ket
  exact UnitaryOperator.ofPerm_applyVec_ket (MeasuredPointAddition.targetPermutation E Q).symm
    value

/-- The complete independent operator applies its basis permutation and retains any reference. -/
lemma stepTarget_apply_ket {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) {Reference : Register}
    (value : (readyContext p.size count).register.Index) (reference : Reference.Index) :
    (stepTarget E Q active Reference).applyVec (NormalizedVector.ket (value, reference)).vec =
      (NormalizedVector.ket (stepPermutation E Q active value, reference)).vec := by
  let original := pointBasis p.size active value
  let relabeled := ContextRelabeling.referenceBasis
    (source := MeasuredPointAddition.context p.size) (storageMap p.size active)
    (physicalMap p.size active) (Register.prod (ambientContext p.size active).register Reference)
  let split := ContextUnion.referenceBasis
    (MeasuredPointAddition.Placement.context p.size (storageMap p.size active)
      (physicalMap p.size active)) (ambientContext p.size active)
    (ambient_disjoint p.size active) Reference
  let placed := ContextPermutation.referenceBasis (framed_entries p.size active) Reference
  have assembly (point : (MeasuredPointAddition.context p.size).register.Index)
      (ambient : (ambientContext p.size active).register.Index) :
      placed (split.symm (relabeled (point, (ambient, reference)))) =
        ((pointBasis p.size active).symm (point, ambient), reference) := rfl
  have pointAction := originalTarget_apply_ket E Q
    (Reference := Register.prod (ambientContext p.size active).register Reference)
    original.1 (original.2, reference)
  have relabeledAction := MeasuredPointAddition.operator_reindex_ket relabeled _ _ _ pointAction
  have framedAction := MeasuredPointAddition.operator_reindex_ket split.symm _ _ _ relabeledAction
  have actual := MeasuredPointAddition.operator_reindex_ket placed _ _ _ framedAction
  rw [assembly, assembly] at actual
  simpa only [stepTarget, MeasuredPointAddition.Placement.Framing.target,
    MeasuredPointAddition.Placement.target, stepPermutation, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, original, placed, split, relabeled,
    Prod.eta, Equiv.symm_apply_apply] using actual

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
