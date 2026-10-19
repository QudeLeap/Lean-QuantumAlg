/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Semantics
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Specification
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.QFT.Mathematics

/-!
# Intrinsic ECDLP amplitudes from the granted group action

The range preparations, original encoded group shift and two inverse Fourier
transforms determine every raw point-bank amplitude. Unused point codes have
zero post-query amplitude. The formulas are symbolic in the original order
and field parameters [PZ03, ecc.tex:321-366,1531-1666].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem Layout.pointEncoding

/-- Full binary basis, including every unused raw point code. -/
@[expose] public def rawBasis (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) : Fin (2 ^ Layout.totalQubits I) :=
  prodEquiv (prodEquiv (left, right), tail)

/-- The fixed identity-inclusive binary label of an actual curve point. -/
public def pointLabel (point : GroupPoint E) : Fin (2 ^ Layout.pointWidth E) :=
  (Layout.pointEncoding E).encode point

/-- The intrinsic binary labels distinguish all actual points. -/
public lemma pointLabel_injective : Function.Injective (pointLabel (E := E)) :=
  (Layout.pointEncoding E).encode_injective

/-- Independent group-action amplitude before Fourier readout. -/
@[expose] public def postQueryCoefficient (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) : ℂ :=
  if right.val < I.subgroupOrder then
    if left.val < I.subgroupOrder then
      if tail = pointLabel
          ((problem I).toSourceScope.oracleMultiplier left.val right.val) then
        FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder *
          FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder
      else 0
    else 0
  else 0

private lemma preparedState_rawBasis (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) :
    preparedState I (rawBasis I left right tail) =
      if tail = (Layout.pointEncoding E).encode 1 then
        if right.val < I.subgroupOrder then
          if left.val < I.subgroupOrder then
            FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder *
              FiniteCyclicDLP.OrderPreparation.invSqrtOrder I.subgroupOrder
          else 0
        else 0
      else 0 := by
  simp [preparedState, rawBasis, FiniteCyclicDLP.OrderPreparation.state_apply,
    NormalizedVector.ket_apply, problem]

private lemma oracle_identity_column (I : ECDLPInstance E) (A : Access I)
    (row : Fin (2 ^ Layout.totalQubits I))
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I))) :
    A.operator row (rawBasis I left right ((Layout.pointEncoding E).encode 1)) =
      if row = rawBasis I left right
          ((Layout.pointEncoding E).encode
            ((problem I).toSourceScope.oracleMultiplier left.val right.val)) then 1 else 0 := by
  have action := congrArg (fun state => state row) (A.basisAction left right 1)
  change A.operator.applyVec
    (NormalizedVector.ket (R := Qubits (Layout.totalQubits I)) (basisIndex I left right 1) :
      HilbertVector (Qubits (Layout.totalQubits I))) row = _ at action
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at action
  simp only [basisIndex, Layout.fullEncoding, BinaryLabelEncoding.prod,
    BinaryLabelEncoding.finIdentity_encode, one_mul] at action
  exact action

/-- The granted action determines the complete actual post-query state. -/
public lemma postQueryState_rawBasis (I : ECDLPInstance E) (A : Access I)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) :
    A.operator.apply (preparedState I) (rawBasis I left right tail) =
      postQueryCoefficient I left right tail := by
  classical
  change (∑ source : Fin (2 ^ Layout.totalQubits I),
    A.operator (rawBasis I left right tail) source * preparedState I source) = _
  rw [← Equiv.sum_comp
    (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I) +
      FiniteCyclicDLP.orderWidth (problem I)) (n := Layout.pointWidth E)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I))
      (n := FiniteCyclicDLP.orderWidth (problem I))), Fintype.sum_prod_type]
  change (∑ sourceLeft : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
    ∑ sourceRight : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
    ∑ sourceTail : Fin (2 ^ Layout.pointWidth E),
      A.operator (rawBasis I left right tail) (rawBasis I sourceLeft sourceRight sourceTail) *
        preparedState I (rawBasis I sourceLeft sourceRight sourceTail)) = _
  simp_rw [preparedState_rawBasis]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq']
  simp_rw [oracle_identity_column]
  rw [Fintype.sum_eq_single left]
  · rw [Fintype.sum_eq_single right]
    · simp [rawBasis, postQueryCoefficient, pointLabel]
      rfl
    · intro sourceRight different
      simp [rawBasis, Ne.symm different]
  · intro sourceLeft different
    simp [rawBasis, Ne.symm different]

/-- Independent double inverse-Fourier sum for every physical output label. -/
@[expose] public def sourceAmplitude (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) : ℂ :=
  ∑ sourceLeft : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
    ∑ sourceRight : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
      star (invSqrtN (FiniteCyclicDLP.orderWidth (problem I)) *
        ω (FiniteCyclicDLP.orderWidth (problem I)) ^ (sourceLeft.val * left.val)) *
      star (invSqrtN (FiniteCyclicDLP.orderWidth (problem I)) *
        ω (FiniteCyclicDLP.orderWidth (problem I)) ^ (sourceRight.val * right.val)) *
      postQueryCoefficient I sourceLeft sourceRight tail

private lemma inverseFourier_entry (width : Nat) (row column : Fin (2 ^ width)) :
    (star (QFTOperator width) : UnitaryOperator (Qubits width)) row column =
      star (invSqrtN width * ω width ^ (column.val * row.val)) := by
  change star (QFTOperator width column row) = _
  rw [QFTOperator_entry]

/-- The actual terminal state has the source amplitude on all raw codes. -/
public lemma sourceState_rawBasis (I : ECDLPInstance E) (A : Access I)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) :
    sourceState I A (rawBasis I left right tail) = sourceAmplitude I left right tail := by
  classical
  change (∑ source : Fin (2 ^ Layout.totalQubits I),
    (((star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))).tensor
      (star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I))))).tensor
        (1 : UnitaryOperator (Qubits (Layout.pointWidth E))))
        (rawBasis I left right tail) source *
      A.operator.apply (preparedState I) source) = _
  rw [← Equiv.sum_comp
    (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I) +
      FiniteCyclicDLP.orderWidth (problem I)) (n := Layout.pointWidth E)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I))
      (n := FiniteCyclicDLP.orderWidth (problem I))), Fintype.sum_prod_type]
  simp only [rawBasis, UnitaryOperator.tensor_apply, Equiv.symm_apply_apply]
  change (∑ sourceLeft : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
    ∑ sourceRight : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)),
    ∑ sourceTail : Fin (2 ^ Layout.pointWidth E),
      ((star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))) left sourceLeft *
        (star (QFTOperator (FiniteCyclicDLP.orderWidth (problem I)))) right sourceRight *
        (1 : Matrix _ _ ℂ) tail sourceTail) *
      A.operator.apply (preparedState I) (rawBasis I sourceLeft sourceRight sourceTail)) = _
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Fintype.sum_ite_eq]
  simp_rw [postQueryState_rawBasis]
  simp only [inverseFourier_entry, sourceAmplitude]

/-- Independent Fourier amplitude in the complete physical binary register. -/
@[expose] public def sourceAmplitudeAt (I : ECDLPInstance E)
    (label : Fin (2 ^ Layout.totalQubits I)) : ℂ :=
  let full := (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I) +
    FiniteCyclicDLP.orderWidth (problem I)) (n := Layout.pointWidth E)).symm label
  let exponents := (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I))
    (n := FiniteCyclicDLP.orderWidth (problem I))).symm full.1
  sourceAmplitude I exponents.1 exponents.2 full.2

/-- The full actual source state is independent of the query's unused columns. -/
public lemma sourceState_eq_sourceAmplitudeAt (I : ECDLPInstance E) (A : Access I)
    (label : Fin (2 ^ Layout.totalQubits I)) :
    sourceState I A label = sourceAmplitudeAt I label := by
  let full := (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I) +
    FiniteCyclicDLP.orderWidth (problem I)) (n := Layout.pointWidth E)).symm label
  let exponents := (prodEquiv (m := FiniteCyclicDLP.orderWidth (problem I))
    (n := FiniteCyclicDLP.orderWidth (problem I))).symm full.1
  have amplitude := sourceState_rawBasis I A exponents.1 exponents.2 full.2
  simpa only [rawBasis, exponents, full, Prod.mk.eta, Equiv.apply_symm_apply, sourceAmplitudeAt]
    using amplitude

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
