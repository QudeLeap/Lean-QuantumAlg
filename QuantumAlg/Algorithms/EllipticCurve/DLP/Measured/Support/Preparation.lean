/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Framing
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Reference
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation.State
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Montgomery

/-!
# Actual original exponent preparation on the supplied Montgomery seed

The normalized vector is the action of the original physically framed range
preparation circuit on its actual zero-exponent input. Its expansion retains
the supplied coordinate words, the original product amplitudes, and an
arbitrary normalized reference vector without measuring any branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open MeasuredUncompute MAU.Inversion.SharedEEA

universe u

/-- The original two independent exact range preparations give this complex product amplitude. -/
def preparedBranchAmplitude {G : Type u} [Group G]
    (problem : FiniteCyclicDLP.KnownOrderProblem G)
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) : ℂ :=
  FiniteCyclicDLP.Concrete.BornBridge.exponentState problem branch.1 *
    FiniteCyclicDLP.Concrete.BornBridge.exponentState problem branch.2

/-- The actual original double preparation has precisely the original product-amplitude column. -/
theorem exponentPreparation_zero_entry {G : Type u} [Group G]
    (problem : FiniteCyclicDLP.KnownOrderProblem G)
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) :
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem).binaryMatrix
      (prodEquiv branch) (prodEquiv (0, 0)) = preparedBranchAmplitude problem branch := by
  have prepared := congrArg (fun vector => vector (prodEquiv branch))
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit_apply_zero problem)
  have zeroPair : prodEquiv
      ((0 : Fin (2 ^ FiniteCyclicDLP.orderWidth problem)), 0) =
        (0 : Fin (2 ^ (FiniteCyclicDLP.orderWidth problem +
          FiniteCyclicDLP.orderWidth problem))) :=
    Fin.ext (by simp [UnitaryCircuit.prodEquiv_value])
  change (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit
      problem).binaryMatrix.applyVec
        (NormalizedVector.ket (R := Qubits
          (FiniteCyclicDLP.orderWidth problem + FiniteCyclicDLP.orderWidth problem)) 0)
        (prodEquiv branch) =
      (FiniteCyclicDLP.OrderPreparation.state problem).tensor
        (FiniteCyclicDLP.OrderPreparation.state problem) (prodEquiv branch) at prepared
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at prepared
  have right :
      (FiniteCyclicDLP.OrderPreparation.state problem).tensor
        (FiniteCyclicDLP.OrderPreparation.state problem) (prodEquiv branch) =
      preparedBranchAmplitude problem branch := by
    exact (NormalizedVector.tensor_apply_prod
      (FiniteCyclicDLP.OrderPreparation.state problem)
      (FiniteCyclicDLP.OrderPreparation.state problem) branch.1 branch.2).trans (by
        simp only [FiniteCyclicDLP.OrderPreparation.state_apply,
          FiniteCyclicDLP.Concrete.BornBridge.exponentState_apply,
          preparedBranchAmplitude, FiniteCyclicDLP.OrderPreparation.invSqrtOrder,
          FiniteCyclicDLP.invSqrtOrder])
  simpa only [zeroPair] using prepared.trans right

/-- Original paired exponent labels remain distinct beside the supplied coordinate words. -/
theorem preparedInputLabel_injective (modulus exponentWidth : Nat)
    (x y : Fin (2 ^ modulus.size)) : Function.Injective
    (fun branch => inputLabel modulus.size (2 * exponentWidth)
      (pairedExponentInput modulus exponentWidth branch) x y) := by
  intro left right same
  have exponentSame := congrArg
    (fun input => (ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
      (exponents modulus.size (2 * exponentWidth))
      (input_disjoint modulus.size (2 * exponentWidth)) input).2) same
  simp only [inputLabel, Equiv.apply_symm_apply] at exponentSame
  exact pairedExponentInput_injective modulus exponentWidth exponentSame

private theorem inputLabel_paired_eq (modulus exponentWidth : Nat)
    (left right : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (leftX leftY rightX rightY : Fin (2 ^ modulus.size)) :
    inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth left) leftX leftY =
      inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth right) rightX rightY ↔
      (leftX, leftY) = (rightX, rightY) ∧ left = right := by
  constructor
  · intro same
    have both := (ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
      (exponents modulus.size (2 * exponentWidth))
      (input_disjoint modulus.size (2 * exponentWidth))).symm.injective same
    exact ⟨(InversePreparation.inputBasisEquiv modulus.size).symm.injective
      (congrArg Prod.fst both), pairedExponentInput_injective modulus exponentWidth
        (congrArg Prod.snd both)⟩
  · rintro ⟨coordinateSame, rfl⟩
    have coordinates := Prod.mk.inj coordinateSame
    rcases coordinates with ⟨rfl, rfl⟩
    rfl

/-- The exact actual pre-work preparation acts on the original caller's zero exponent pair. -/
def preparedInputVector {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) (x y : Fin (2 ^ modulus.size)) :
    NormalizedVector (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem)).register :=
  ((beforeExponentProgram modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)).matrix).apply
    (NormalizedVector.ket (inputLabel modulus.size
      (2 * FiniteCyclicDLP.orderWidth problem)
      (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) (0, 0)) x y))

private theorem preparedInputVector_entry {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) (x y : Fin (2 ^ modulus.size))
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) (rowX rowY : Fin (2 ^ modulus.size)) :
    preparedInputVector modulus problem x y (inputLabel modulus.size
      (2 * FiniteCyclicDLP.orderWidth problem)
      (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) branch) rowX rowY) =
      (if (rowX, rowY) = (x, y) then 1 else 0) * preparedBranchAmplitude problem branch := by
  have column := HilbertOperator.applyVec_ket
    (R := (before modulus.size (2 * FiniteCyclicDLP.orderWidth problem)).register)
    ((beforeExponentProgram modulus (FiniteCyclicDLP.orderWidth problem)
      (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)).matrix)
    (inputLabel modulus.size (2 * FiniteCyclicDLP.orderWidth problem)
      (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) (0, 0)) x y)
    (inputLabel modulus.size (2 * FiniteCyclicDLP.orderWidth problem)
      (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) branch) rowX rowY)
  have entry := beforeExponentProgram_paired_entry modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
    branch (0, 0) rowX rowY x y
  rw [exponentPreparation_zero_entry] at entry
  exact column.trans entry

/-- Actual normalized preparation has its exact coherent expansion on every original branch. -/
theorem preparedInputVector_expansion {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) (x y : Fin (2 ^ modulus.size)) :
    (∑ branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
        Fin (2 ^ FiniteCyclicDLP.orderWidth problem),
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (inputLabel modulus.size
          (2 * FiniteCyclicDLP.orderWidth problem)
          (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) branch) x y) :
          HilbertVector (before modulus.size
            (2 * FiniteCyclicDLP.orderWidth problem)).register)) =
      (preparedInputVector modulus problem x y).vec := by
  classical
  apply WithLp.ofLp_injective
  funext row
  obtain ⟨exponent, rowX, rowY, rfl⟩ := inputLabel_surjective modulus.size
    (2 * FiniteCyclicDLP.orderWidth problem) row
  obtain ⟨branch, rfl⟩ := pairedExponentInput_surjective modulus
    (FiniteCyclicDLP.orderWidth problem) exponent
  change _ = preparedInputVector modulus problem x y (inputLabel modulus.size
    (2 * FiniteCyclicDLP.orderWidth problem)
    (pairedExponentInput modulus (FiniteCyclicDLP.orderWidth problem) branch) rowX rowY)
  rw [preparedInputVector_entry]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    NormalizedVector.ket_apply, inputLabel_paired_eq]
  by_cases same : (rowX, rowY) = (x, y)
  · simp [same]
  · simp [same]

/-- The supplied Montgomery seed is the actual original two-word source label on each branch. -/
theorem pairedMontgomeryInput_injective {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E) :
    Function.Injective (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed) := by
  intro left right same
  apply preparedInputLabel_injective p exponentWidth
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
        (Fact.out : Nat.Prime p).pos fits seed.x))
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
        (Fact.out : Nat.Prime p).pos fits seed.y))
  exact same

/-- The actual original preparation keeps the supplied Montgomery seed and arbitrary reference. -/
def preparedMontgomeryVector {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (Register.prod
      (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register Reference) :=
  normalizedReferenceFrame (preparedInputVector p problem
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
        (Fact.out : Nat.Prime p).pos fits seed.x))
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
        (Fact.out : Nat.Prime p).pos fits seed.y))) reference

/-- The complete reference-framed expansion uses the original branch amplitudes unchanged. -/
theorem preparedMontgomeryVector_expansion {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    referenceFrame (∑ branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
        Fin (2 ^ FiniteCyclicDLP.orderWidth problem),
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (pairedMontgomeryInput fieldTail
          (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch) :
          HilbertVector (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register))
      reference.vec =
      (preparedMontgomeryVector problem fieldTail sameWidth fits seed reference).vec := by
  unfold pairedMontgomeryInput montgomeryInput
  rw [preparedInputVector_expansion]
  rfl

/-- The complete normalized vector is precisely the actual framed circuit's action. -/
theorem preparedMontgomeryVector_actual {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    (beforeExponentOperator p (FiniteCyclicDLP.orderWidth problem)
      (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
      Reference).applyVec
        (normalizedReferenceFrame (NormalizedVector.ket (pairedMontgomeryInput fieldTail
          (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed (0, 0))) reference).vec =
      (preparedMontgomeryVector problem fieldTail sameWidth fits seed reference).vec := by
  exact referenceFrame_unitary _ _ _

/-- The actual preparation's complete joint density is the certified prepared pure density. -/
theorem preparedMontgomeryVector_density {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    DensityOperator.applyUnitary
      (beforeExponentOperator p (FiniteCyclicDLP.orderWidth problem)
        (FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit problem)
        Reference)
      (DensityOperator.ofPure (normalizedReferenceFrame
        (NormalizedVector.ket (pairedMontgomeryInput fieldTail
          (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed (0, 0))) reference)) =
      DensityOperator.ofPure
        (preparedMontgomeryVector problem fieldTail sameWidth fits seed reference) := by
  rw [← DensityOperator.ofPure_apply]
  congr 1
  apply NormalizedVector.ext
  intro label
  exact congrArg (fun vector => vector label)
    (preparedMontgomeryVector_actual problem fieldTail sameWidth fits seed reference)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
