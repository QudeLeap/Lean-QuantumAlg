/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Ideal.Kernel
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.FullFrequencyOrthogonality
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix

/-!
# The unchanged ideal branch effect as a complete pair-frequency kernel

The existing ideal effect already retains both original exponent labels, its
full group output and an arbitrary Reference. Its exact matrix formula is
reindexed over every canonical pair frequency. The readout rows are the same
complete native inverse Fourier rows, in second-times-first scalar order.

No input support, good-source, normalization or width premise is needed. This
module changes neither the ideal effect nor the actual execution, and proves
no comparison or success lower bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace IdealFrequencyKernel

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP ConcreteCircuitAccess QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open ECDLP.Measured
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

universe u

/-- The original paired readout is exactly the two actual complete native rows. -/
lemma readout_pairRows {G : Type u} [Group G] (problem : KnownOrderProblem G)
    (frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (source : Bits (orderWidth problem) × Bits (orderWidth problem)) :
    ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation) (prodEquiv
      frequency)
        (prodEquiv (binaryEquiv (orderWidth problem) source.1,
          binaryEquiv (orderWidth problem) source.2)) =
      FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency source := by
  rw [exponentReadoutCircuit_binaryMatrix, UnitaryOperator.tensor_apply]
  simp only [Equiv.symm_apply_apply]
  simp only [FullFrequencyOrthogonality.pairRows, Partner.fullRows, if_true,
    Native.qftNative_inverseCircuit_binaryMatrix]
  exact mul_comm _ _

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every original paired frequency occurs once in the exact complex Fourier event kernel. -/
lemma idealFourierEventKernel_frequency (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (left right : (idealBranchRegister problem).Index) :
    IdealKernel.idealFourierEventKernel problem event left right =
      ∑ frequency : (idealBranchRegister problem).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) = true then
          star (((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
            (prodEquiv frequency) (prodEquiv left)) *
            ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
              (prodEquiv frequency) (prodEquiv right)
        else 0 := by
  unfold IdealKernel.idealFourierEventKernel
  symm
  let coordinates : (idealBranchRegister problem).Index ≃
      (Qubits (orderWidth problem + orderWidth problem)).Index :=
    prodEquiv (m := orderWidth problem) (n := orderWidth problem)
  refine Finset.sum_bij (fun frequency _ => coordinates frequency) ?_ ?_ ?_ ?_
  · intro frequency _
    exact Finset.mem_univ _
  · intro first _ second _ same
    exact coordinates.injective same
  · intro output _
    exact ⟨coordinates.symm output, Finset.mem_univ _, coordinates.apply_symm_apply output⟩
  · intro frequency _
    dsimp only [coordinates]
    have undone :
        (prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm
            (prodEquiv frequency) = frequency :=
      (prodEquiv (m := orderWidth problem) (n := orderWidth problem)).symm_apply_apply frequency
    exact if_congr
      (Iff.of_eq (congrArg
        (fun value : (idealBranchRegister problem).Index =>
          event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            value) = true) undone.symm)) rfl rfl

/-- The full ideal observable keeps precisely the group and Reference deltas at each frequency. -/
lemma idealBranchEffect_matrix_frequency (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) (left right : ((idealBranchRegister problem).prod Reference).Index) :
    (idealBranchEffect problem seed event Reference).matrix left right =
      ∑ frequency : (idealBranchRegister problem).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) = true then
          (star (((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
              (prodEquiv frequency) (prodEquiv left.1)) *
            ((exponentReadoutCircuit problem).binaryMatrix OracleModel.emptyInterpretation)
              (prodEquiv frequency) (prodEquiv right.1)) *
            (if idealGroupOutput problem seed left.1 = idealGroupOutput problem seed right.1 ∧
                left.2 = right.2 then 1 else 0)
        else 0 := by
  rw [IdealKernel.idealBranchEffect_matrix, idealFourierEventKernel_frequency]
  have groupOutput :
      idealGroupOutput problem seed left.1 = idealGroupOutput problem seed right.1 ↔
        problem.toSourceScope.oracleMultiplier left.1.1.val left.1.2.val =
          problem.toSourceScope.oracleMultiplier right.1.1.val right.1.2.val := by
    change seed.toGroupPoint * _ = seed.toGroupPoint * _ ↔ _
    exact mul_left_cancel_iff
  by_cases groupSame :
      problem.toSourceScope.oracleMultiplier left.1.1.val left.1.2.val =
        problem.toSourceScope.oracleMultiplier right.1.1.val right.1.2.val
  · by_cases referenceSame : left.2 = right.2
    · have both :
          idealGroupOutput problem seed left.1 = idealGroupOutput problem seed right.1 ∧
            left.2 = right.2 := ⟨groupOutput.mpr groupSame, referenceSame⟩
      simp only [if_pos groupSame, if_pos referenceSame, one_mul, if_pos both, mul_one]
    · have different :
          ¬(idealGroupOutput problem seed left.1 = idealGroupOutput problem seed right.1 ∧
            left.2 = right.2) := fun both => referenceSame both.2
      simp only [if_neg referenceSame, if_neg different, mul_zero, zero_mul, ite_self,
        Finset.sum_const_zero]
  · have different :
        ¬(idealGroupOutput problem seed left.1 = idealGroupOutput problem seed right.1 ∧
          left.2 = right.2) := fun both => groupSame (groupOutput.mp both.1)
    simp only [if_neg groupSame, if_neg different, zero_mul, mul_zero, ite_self,
      Finset.sum_const_zero]

/-- Binary source tuples give the literal actual pairRows kernel of the unchanged ideal effect. -/
lemma idealBranchEffect_matrix_pairRows (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register)
    (left right : Bits (orderWidth problem) × Bits (orderWidth problem))
    (refLeft refRight : Reference.Index) :
    (idealBranchEffect problem seed event Reference).matrix
        ((binaryEquiv (orderWidth problem) left.1, binaryEquiv (orderWidth problem) left.2),
          refLeft)
        ((binaryEquiv (orderWidth problem) right.1, binaryEquiv (orderWidth problem) right.2),
          refRight) =
      ∑ frequency : (idealBranchRegister problem).Index,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) = true then
          (star (FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency left) *
            FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency right) *
            (if idealGroupOutput problem seed
                  (binaryEquiv (orderWidth problem) left.1,
                    binaryEquiv (orderWidth problem) left.2) =
                idealGroupOutput problem seed
                  (binaryEquiv (orderWidth problem) right.1,
                    binaryEquiv (orderWidth problem) right.2) ∧ refLeft = refRight
              then 1 else 0)
        else 0 := by
  rw [idealBranchEffect_matrix_frequency]
  apply Finset.sum_congr rfl
  intro frequency _
  let groupDelta : ℂ :=
    if idealGroupOutput problem seed
          (binaryEquiv (orderWidth problem) left.1, binaryEquiv (orderWidth problem) left.2) =
        idealGroupOutput problem seed
          (binaryEquiv (orderWidth problem) right.1, binaryEquiv (orderWidth problem) right.2) ∧
          refLeft = refRight then 1 else 0
  exact congrArg₂
    (fun first second : ℂ =>
      if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
          frequency) = true then (star first * second) * groupDelta else 0)
    (readout_pairRows (problem := problem) (frequency := frequency) (source := left))
    (readout_pairRows (problem := problem) (frequency := frequency) (source := right))

end

end IdealFrequencyKernel
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
