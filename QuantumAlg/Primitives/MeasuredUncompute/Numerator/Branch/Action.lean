/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.HadamardMatrix
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Conjugation

/-!
# Basis action of the actual stored numerator branch

The operator already identified with the H/Z/write/read/X interpreter has
one exact column for each complete input basis label: the original prefix
is retained, Y becomes zero, and the original numerator contributes its
Walsh character. The external reference is unchanged, including arbitrary
correlations after linear extension [LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorBranchAction

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation
open NumeratorResetMatrix

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Replace only the actual numerator coordinates of a complete runtime basis label. -/
def replaceWord (width : Nat) (basis : (context width).register.Index)
    (value : Fin (2 ^ width)) : (context width).register.Index :=
  (frameBasis width).symm (prodEquiv (framePrefix width basis, value))

private lemma replace_frame (width : Nat) (basis : (context width).register.Index)
    (value : Fin (2 ^ width)) :
    frameBasis width (replaceWord width basis value) =
      prodEquiv (framePrefix width basis, value) :=
  (frameBasis width).apply_symm_apply _

/-- The complete prefix and the measured word characterize replacement exactly. -/
lemma eq_replace_iff (width : Nat) (row basis : (context width).register.Index)
    (value : Fin (2 ^ width)) :
    row = replaceWord width basis value ↔
      framePrefix width row = framePrefix width basis ∧ word width row = value := by
  have coordinates := (congrArg
    (fun label : Fin (2 ^ (OutputCopy.encoding width).width) =>
      (prodEquiv (m := (encoding width).width) (n := width)).symm label)
    (replace_frame width basis value)).trans
      ((prodEquiv (m := (encoding width).width) (n := width)).symm_apply_apply
        (framePrefix width basis, value))
  constructor
  · intro same
    subst row
    have first := congrArg (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) =>
      pair.1) coordinates
    have second := congrArg (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) =>
      pair.2) coordinates
    exact ⟨first, second⟩
  · intro same
    apply (frameBasis width).injective
    apply (prodEquiv (m := (encoding width).width) (n := width)).symm.injective
    have pair : (prodEquiv (m := (encoding width).width) (n := width)).symm
        (frameBasis width row) = (framePrefix width basis, value) :=
      Prod.ext same.1 same.2
    exact pair.trans coordinates.symm

/-- Replacement preserves all unmeasured coordinates and sets precisely the requested word. -/
lemma replace_coordinates (width : Nat) (basis : (context width).register.Index)
    (value : Fin (2 ^ width)) :
    framePrefix width (replaceWord width basis value) = framePrefix width basis ∧
      word width (replaceWord width basis value) = value :=
  (eq_replace_iff width _ basis value).mp rfl

/-- Actual H followed by the stored Z projection has one complete reference-labelled output ket. -/
lemma projected_hadamard_ket (width : Nat) {Reference : Register}
    (stored : Store (context width)) (basis : (context width).register.Index)
    (reference : Reference.Index) :
    HilbertOperator.applyVec (ZMeasurement.projector
        (fun entry : (Register.prod (context width).register Reference).Index => word width entry.1)
        (NumeratorReset.outcome (stored.read (input width))) *
      (UnitaryOperator.prodTensor
        ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix environment)
        (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod (context width).register Reference)))
      (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        (basis, reference)).vec =
      (WalshHadamard.invSqrtCard width *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input width)))
          (word width basis)) •
        (NormalizedVector.ket (R := Register.prod (context width).register Reference)
          (replaceWord width basis (NumeratorReset.outcome (stored.read (input width))),
            reference)).vec := by
  ext ⟨row, other⟩
  rw [HilbertOperator.applyVec_ket, ZMeasurement.projector, Matrix.diagonal_mul,
    UnitaryOperator.prodTensor_apply, NumeratorHadamardMatrix.hadamard_entry]
  change (if word width row = NumeratorReset.outcome (stored.read (input width)) then
      (1 : ℂ) else 0) *
    ((if framePrefix width row = framePrefix width basis then
      WalshHadamard.invSqrtCard width * WalshHadamard.walshSign (word width row)
        (word width basis) else 0) * (if other = reference then 1 else 0)) =
      (WalshHadamard.invSqrtCard width *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input width)))
          (word width basis)) *
        (NormalizedVector.ket (R := Register.prod (context width).register Reference)
          (replaceWord width basis (NumeratorReset.outcome (stored.read (input width))),
            reference)) (row, other)
  rw [NormalizedVector.ket_apply]
  have joint : ((row, other) : (Register.prod (context width).register Reference).Index) =
      (replaceWord width basis (NumeratorReset.outcome (stored.read (input width))), reference) ↔
      (framePrefix width row = framePrefix width basis ∧
        word width row = NumeratorReset.outcome (stored.read (input width))) ∧
        other = reference := by
    constructor
    · intro same
      exact ⟨(eq_replace_iff width row basis _).mp (congrArg Prod.fst same),
        congrArg Prod.snd same⟩
    · intro same
      exact Prod.ext ((eq_replace_iff width row basis _).mpr same.1) same.2
  simp only [joint]
  by_cases measured : word width row = NumeratorReset.outcome (stored.read (input width)) <;>
    by_cases samePrefix : framePrefix width row = framePrefix width basis <;>
    by_cases sameReference : other = reference <;>
    simp [measured, samePrefix, sameReference]

/-- The actually selected reset keeps both the complete prefix and the external reference. -/
lemma reset_replaced_ket (width : Nat) {Reference : Register}
    (stored : Store (context width)) (basis : (context width).register.Index)
    (reference : Reference.Index) :
    (UnitaryOperator.prodTensor
      ((NumeratorRuntime.program width
        (NumeratorReset.member width (stored.read (input width)))).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        (replaceWord width basis (NumeratorReset.outcome (stored.read (input width))),
          reference)).vec =
      (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        (replaceWord width basis 0, reference)).vec := by
  ext ⟨row, other⟩
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor
      ((NumeratorRuntime.program width
        (NumeratorReset.member width (stored.read (input width)))).matrix environment)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference))
    (NormalizedVector.ket (R := Register.prod (context width).register Reference)
      (replaceWord width basis (NumeratorReset.outcome (stored.read (input width))),
        reference)).vec (row, other) = _
  rw [HilbertOperator.applyVec_ket, UnitaryOperator.prodTensor_apply,
    member_column width _ _ row (replace_coordinates width basis _).2]
  rw [(replace_coordinates width basis _).1]
  have equal : frameBasis width row = prodEquiv (framePrefix width basis, (0 : Fin (2 ^ width))) ↔
      row = replaceWord width basis 0 := by
    rw [← replace_frame width basis 0]
    exact (frameBasis width).injective.eq_iff
  have column :
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (framePrefix width basis, (0 : Fin (2 ^ width)))))
          (frameBasis width row) = if row = replaceWord width basis 0 then (1 : ℂ) else 0 := by
    refine (NormalizedVector.ket_apply (R := Qubits (OutputCopy.encoding width).width)
      (prodEquiv (framePrefix width basis, (0 : Fin (2 ^ width))))
      (frameBasis width row)).trans ?_
    simp only [equal]
  rw [column]
  change (if row = replaceWord width basis 0 then (1 : ℂ) else 0) *
      (if other = reference then 1 else 0) =
    (NormalizedVector.ket (R := Register.prod (context width).register Reference)
      (replaceWord width basis 0, reference)) (row, other)
  rw [NormalizedVector.ket_apply]
  have joint : ((row, other) : (Register.prod (context width).register Reference).Index) =
      (replaceWord width basis 0, reference) ↔ row = replaceWord width basis 0 ∧
        other = reference := by
    constructor
    · intro same
      exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · intro same
      exact Prod.ext same.1 same.2
  simp only [joint]
  by_cases same : row = replaceWord width basis 0 <;>
    by_cases refSame : other = reference <;> simp [same, refSame]

/-- The full actual H/Z/stored-X matrix keeps exactly the original numerator character. -/
lemma operator_ket (width : Nat) {Reference : Register}
    (stored : Store (context width)) (basis : (context width).register.Index)
    (reference : Reference.Index) :
    (NumeratorResetConjugation.operator environment width Reference stored).applyVec
      (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        (basis, reference)).vec =
      (WalshHadamard.invSqrtCard width *
        WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input width)))
          (word width basis)) •
        (NormalizedVector.ket (R := Register.prod (context width).register Reference)
          (replaceWord width basis 0, reference)).vec := by
  rw [NumeratorResetConjugation.operator, Matrix.mul_assoc, HilbertOperator.mul_applyVec,
    projected_hadamard_ket, HilbertOperator.applyVec_smul]
  exact congrArg (fun vector =>
    (WalshHadamard.invSqrtCard width *
      WalshHadamard.walshSign (NumeratorReset.outcome (stored.read (input width)))
        (word width basis)) • vector) (reset_replaced_ket width stored basis reference)

end

end QuantumAlg.MeasuredUncompute.NumeratorBranchAction
