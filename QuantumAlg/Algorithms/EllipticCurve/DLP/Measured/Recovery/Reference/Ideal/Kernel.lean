/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all QuantumAlg.Core.Base.Gate.Effect.Embedding
import all QuantumAlg.Core.Base.Gate.Effect.Unitary
import all QuantumAlg.Core.Measure.Instrument

/-!
# Original finite Fourier mathematics without an execution compiler

The source frequencies, full-group fibers, arbitrary reference, coherent
cross terms and original oversampling remain unchanged. This module is
mathematical only. It defines no physical preparation or algorithm, and
establishes no comparison with the streaming execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.IdealKernel

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Execution FiniteCyclicDLP ConcreteCircuitAccess
open ECDLP.Measured
open scoped BigOperators ComplexOrder

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The unchanged inverse-QFT columns give the exact complex event kernel. -/
def idealFourierEventKernel (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (left right : (idealBranchRegister problem).Index) : ℂ :=
  ∑ output : (Qubits (orderWidth problem + orderWidth problem)).Index,
    if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        (prodEquiv.symm output)) = true then
      star (((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation) output
        (prodEquiv left)) *
        ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation) output
          (prodEquiv right)
    else 0

/-- Left translation by the same supplied seed preserves exactly the original oracle fibers. -/
lemma idealGroupLabel_eq_iff (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (left right : (idealBranchRegister problem).Index) :
    idealGroupLabel problem seed left = idealGroupLabel problem seed right ↔
      problem.toSourceScope.oracleMultiplier left.1.val left.2.val =
        problem.toSourceScope.oracleMultiplier right.1.val right.2.val := by
  constructor
  · intro same
    have outputSame := congrArg (fun label => label.val) same
    exact mul_left_cancel outputSame
  · intro same
    apply Subtype.ext
    exact congrArg (fun value => seed.toGroupPoint * value) same

private lemma idealBranchEffect_matrix_sum (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) (left right : ((idealBranchRegister problem).prod Reference).Index) :
    (idealBranchEffect problem seed event Reference).matrix left right =
      ∑ output, if idealReadoutEvent problem seed event Reference output = true then
        star ((idealReadoutOperator problem seed Reference) output
          (idealOracleEmbedding problem seed Reference left)) *
          (idealReadoutOperator problem seed Reference) output
            (idealOracleEmbedding problem seed Reference right)
      else 0 := by
  let R := ((Qubits (orderWidth problem + orderWidth problem)).prod
    (idealGroupRegister problem seed)).prod Reference
  change (((idealReadoutOperator problem seed Reference : HilbertOperator R).conjTranspose *
    (idealReadoutEffect problem seed event Reference).matrix) *
      (idealReadoutOperator problem seed Reference : HilbertOperator R))
        (idealOracleEmbedding problem seed Reference left)
        (idealOracleEmbedding problem seed Reference right) = _
  rw [Matrix.mul_assoc]
  simp only [idealReadoutEffect, ZMeasurement.projector]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.conjTranspose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero]

/-- The exact branch observable is its Fourier event kernel times group and reference deltas. -/
lemma idealBranchEffect_matrix (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) (left right : ((idealBranchRegister problem).prod Reference).Index) :
    (idealBranchEffect problem seed event Reference).matrix left right =
      (if problem.toSourceScope.oracleMultiplier left.1.1.val left.1.2.val =
          problem.toSourceScope.oracleMultiplier right.1.1.val right.1.2.val then 1 else 0) *
        (if left.2 = right.2 then 1 else 0) *
          idealFourierEventKernel problem event left.1 right.1 := by
  rw [idealBranchEffect_matrix_sum]
  simp only [idealReadoutOperator, UnitaryOperator.prodTensor_apply,
    idealOracleEmbedding, idealReadoutEvent]
  change (∑ output : ((Fin (2 ^ (orderWidth problem + orderWidth problem)) ×
      (idealGroupRegister problem seed).Index) × Reference.Index),
    if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        (prodEquiv.symm output.1.1)) = true then
      star (((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
        output.1.1 (prodEquiv left.1) *
        (if output.1.2 = idealGroupLabel problem seed left.1 then 1 else 0) *
        (if output.2 = left.2 then 1 else 0)) *
      (((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation) output.1.1
        (prodEquiv right.1) *
        (if output.1.2 = idealGroupLabel problem seed right.1 then 1 else 0) *
        (if output.2 = right.2 then 1 else 0)) else 0) = _
  simp only [Fintype.sum_prod_type]
  by_cases groupSame : idealGroupLabel problem seed left.1 = idealGroupLabel problem seed right.1
  · have multiplierSame := (idealGroupLabel_eq_iff problem seed left.1 right.1).mp groupSame
    by_cases referenceSame : left.2 = right.2
    · simp [groupSame, referenceSame, multiplierSame, idealFourierEventKernel,
        ite_mul, apply_ite]
    · simp [groupSame, referenceSame, Ne.symm referenceSame, multiplierSame, ite_mul, apply_ite]
  · have multiplierDifferent := mt
      (idealGroupLabel_eq_iff problem seed left.1 right.1).mpr groupSame
    simp [Ne.symm groupSame, multiplierDifferent, ite_mul, apply_ite]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.IdealKernel
