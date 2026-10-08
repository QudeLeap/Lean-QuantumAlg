/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout.Initialized
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Ideal.Kernel
import all QuantumAlg.Core.Execution.Measurement.Readout.Effect

/-!
# Exact event kernel on the actual initialized scalar output

The observable is pulled through the same allocated inverse-QFT matrix and
reads the original physical exponent wires. On actual initialized columns it
retains exactly the original coordinate-pair and reference equalities beside
the original complex Fourier event kernel. Coordinate words are unrestricted
here; valid Montgomery point coordinates are connected by their own theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open MAU.Inversion.SharedEEA GenericPointAddition.InPlace
open FiniteCyclicDLP ConcreteCircuitAccess

/-- The actual initialized output reads the original paired big-endian exponent bit. -/
theorem afterExponentWires_initializedValue (modulus exponentWidth : Nat)
    (Reference : Register) (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (x y : Fin (2 ^ modulus.size)) (reference : Reference.Index)
    (index : Fin (2 * exponentWidth)) :
    decide (((initializedOutputEmbedding modulus (2 * exponentWidth) Reference
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch) x y, reference)).1
          (afterExponentWires modulus exponentWidth index)).val = 1) =
      ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index := by
  have assembled := congrArg (fun label => label.1)
    (initializedOutputEmbedding_ready modulus (2 * exponentWidth) Reference
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch) x y, reference))
  rw [← assembled, afterExponentWires_value]
  change decide ((indexedValue modulus.size (2 * exponentWidth)
    ((ContextPermutation.basis (body_entries modulus.size (2 * exponentWidth))).symm
      ((ContextPermutation.basis (body_entries modulus.size (2 * exponentWidth)))
        (initializedReadyBasis modulus (2 * exponentWidth)
          (inputLabel modulus.size (2 * exponentWidth)
            (pairedExponentInput modulus exponentWidth branch) x y)))) index.castSucc).val = 1) = _
  rw [Equiv.symm_apply_apply, initializedReadyBasis_pairedExponentInput]
  cases ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index <;> rfl

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual original-wire observable pulled back through the same allocated inverse Fourier. -/
def afterExponentReadoutEffect (modulus : Nat) (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register) :
    Effect ((after modulus.size (2 * orderWidth problem)).register.prod Reference) :=
  Effect.pullbackUnitary
    (UnitaryOperator.prodTensor
      (afterExponentProgram modulus (orderWidth problem)
        (exponentReadoutCircuit problem)).matrix (1 : UnitaryOperator Reference))
    (QubitReadouts.eventEffect (afterExponentWires modulus (orderWidth problem)) event Reference)

private theorem afterExponentReadoutEffect_matrix_sum (modulus : Nat)
    (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register)
    (left right : ((after modulus.size (2 * orderWidth problem)).register.prod Reference).Index) :
    (afterExponentReadoutEffect modulus problem event Reference).matrix left right =
      ∑ output, if (event fun index => decide
        ((output.1 (afterExponentWires modulus (orderWidth problem) index)).val = 1)) = true then
          star ((UnitaryOperator.prodTensor
            (afterExponentProgram modulus (orderWidth problem)
              (exponentReadoutCircuit problem)).matrix
            (1 : UnitaryOperator Reference)) output left) *
          (UnitaryOperator.prodTensor
            (afterExponentProgram modulus (orderWidth problem)
              (exponentReadoutCircuit problem)).matrix
            (1 : UnitaryOperator Reference)) output right
        else 0 := by
  let R := (after modulus.size (2 * orderWidth problem)).register.prod Reference
  let operator : UnitaryOperator R := UnitaryOperator.prodTensor
    (afterExponentProgram modulus (orderWidth problem)
      (exponentReadoutCircuit problem)).matrix (1 : UnitaryOperator Reference)
  change (((operator : HilbertOperator R).conjTranspose *
    (QubitReadouts.eventEffect (afterExponentWires modulus (orderWidth problem))
      event Reference).matrix) * (operator : HilbertOperator R)) left right = _
  rw [Matrix.mul_assoc]
  simp only [QubitReadouts.eventEffect, ZMeasurement.projector]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.conjTranspose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero]
  rfl

private theorem initialized_kernel_sum
    {Selector Auxiliary Input Output : Type}
    [Finite Selector] [Finite Auxiliary] [Fintype Input] [Fintype Output]
    [selectorDecision : DecidableEq Selector] [auxiliaryDecision : DecidableEq Auxiliary]
    (coordinates : Selector × Auxiliary × Input ≃ Output)
    (selector : Selector) (auxiliary : Auxiliary)
    (outer : Output → Input → ℂ) (inner : Input → Input → ℂ)
    (event : Output → Bool)
    (entries : ∀ selected prepared row column,
      outer (coordinates (selected, prepared, row)) column =
        (if selected = selector then 1 else 0) *
          ((if prepared = auxiliary then 1 else 0) * inner row column))
    (left right : Input) :
    (∑ output, if event output = true then
      star (outer output left) * outer output right else 0) =
      ∑ input, if event (coordinates (selector, auxiliary, input)) = true then
        star (inner input left) * inner input right else 0 := by
  let := Fintype.ofFinite Selector
  let := Fintype.ofFinite Auxiliary
  rw [← coordinates.sum_comp]
  simp only [Fintype.sum_prod_type, entries]
  refine (Finset.sum_eq_single selector ?_ (by simp)).trans ?_
  · intro selected _ different
    simp [different]
  · refine (Finset.sum_eq_single auxiliary ?_ (by simp)).trans ?_
    · intro prepared _ different
      simp [different]
    · simp

private theorem afterExponentReadoutEffect_initialized_sum (modulus : Nat)
    (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register)
    (left right : ((before modulus.size (2 * orderWidth problem)).register.prod Reference).Index) :
    (afterExponentReadoutEffect modulus problem event Reference).matrix
        (initializedOutputEmbedding modulus (2 * orderWidth problem) Reference left)
        (initializedOutputEmbedding modulus (2 * orderWidth problem) Reference right) =
      ∑ output, if (event fun index => decide
        (((initializedOutputEmbedding modulus (2 * orderWidth problem) Reference output).1
          (afterExponentWires modulus (orderWidth problem) index)).val = 1)) = true then
        star ((beforeExponentOperator modulus (orderWidth problem) (exponentReadoutCircuit problem)
          Reference) output left) *
          (beforeExponentOperator modulus (orderWidth problem) (exponentReadoutCircuit problem)
            Reference) output right
        else 0 := by
  rw [afterExponentReadoutEffect_matrix_sum]
  exact initialized_kernel_sum
    (selectorDecision := (indexedLayout modulus.size (2 * orderWidth problem)).register.decEq)
    (auxiliaryDecision := (InputPreparation.auxiliaryLayout modulus.size).register.decEq)
    (initializedJointAssembly modulus (2 * orderWidth problem) Reference)
    (BasisPreparation.zero (indexedLayout modulus.size (2 * orderWidth problem))).value
    (InPlacePreparation.preparation modulus).value
    (fun output input => UnitaryOperator.prodTensor
      (afterExponentProgram modulus (orderWidth problem)
        (exponentReadoutCircuit problem)).matrix (1 : UnitaryOperator Reference)
          output (initializedOutputEmbedding modulus (2 * orderWidth problem) Reference input))
    (beforeExponentOperator modulus (orderWidth problem) (exponentReadoutCircuit problem)
      Reference)
    (fun output => event fun index => decide
      ((output.1 (afterExponentWires modulus (orderWidth problem) index)).val = 1))
    (afterExponentOperator_initializedAssembly_entry modulus (orderWidth problem)
      (exponentReadoutCircuit problem) Reference)
    left right

private def readoutInputBasis (modulus exponentWidth : Nat) (Reference : Register) :
    (((Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) ×
      (Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))) × Reference.Index) ≃
      ((before modulus.size (2 * exponentWidth)).register.prod Reference).Index :=
  Equiv.prodCongr
    ((Equiv.prodCongr (InversePreparation.inputBasisEquiv modulus.size).symm
      (pairedExponentEquiv modulus exponentWidth)).trans
      (ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
        (exponents modulus.size (2 * exponentWidth))
        (input_disjoint modulus.size (2 * exponentWidth))).symm)
    (Equiv.refl Reference.Index)

private theorem readoutInputBasis_apply (modulus exponentWidth : Nat) (Reference : Register)
    (coordinates : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size))
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) (reference : Reference.Index) :
    readoutInputBasis modulus exponentWidth Reference ((coordinates, branch), reference) =
      (inputLabel modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch) coordinates.1 coordinates.2,
        reference) := by
  change ((ContextUnion.unionBasisEquiv (InversePreparation.before modulus.size)
    (exponents modulus.size (2 * exponentWidth))
    (input_disjoint modulus.size (2 * exponentWidth))).symm
      ((InversePreparation.inputBasisEquiv modulus.size).symm coordinates,
        pairedExponentEquiv modulus exponentWidth branch), reference) = _
  rw [pairedExponentEquiv_apply]
  rfl

private theorem paired_kernel_sum {Coordinates Branch Reference Input : Type}
    [Finite Coordinates] [Fintype Branch] [Finite Reference] [Fintype Input]
    [coordinatesDecision : DecidableEq Coordinates] [referenceDecision : DecidableEq Reference]
    (labels : ((Coordinates × Branch) × Reference) ≃ Input)
    (columns : Coordinates → Branch → Reference → Input)
    (operator : Input → Input → ℂ) (fourier : Branch → Branch → ℂ)
    (event : Input → Bool) (selected : Branch → Bool)
    (event_eq : ∀ coordinates branch reference,
      event (labels ((coordinates, branch), reference)) = selected branch)
    (entries : ∀ coordinates branch reference prior column retained,
      operator (labels ((coordinates, branch), reference))
        (columns prior column retained) =
      ((if coordinates = prior then 1 else 0) * fourier branch column) *
        (if reference = retained then 1 else 0))
    (leftCoordinates rightCoordinates : Coordinates) (left right : Branch)
    (leftReference rightReference : Reference) :
    (∑ output, if event output = true then
      star (operator output (columns leftCoordinates left leftReference)) *
        operator output (columns rightCoordinates right rightReference) else 0) =
      (if leftCoordinates = rightCoordinates then 1 else 0) *
        (if leftReference = rightReference then 1 else 0) *
        ∑ branch, if selected branch = true then
          star (fourier branch left) * fourier branch right else 0 := by
  let := Fintype.ofFinite Coordinates
  let := Fintype.ofFinite Reference
  rw [← labels.sum_comp]
  simp only [Fintype.sum_prod_type, event_eq, entries]
  refine (Finset.sum_eq_single rightCoordinates ?_ (by simp)).trans ?_
  · intro coordinates _ different
    simp [different]
  · by_cases coordinatesSame : leftCoordinates = rightCoordinates
    · by_cases referenceSame : leftReference = rightReference
      · simp [coordinatesSame, referenceSame, ite_mul, apply_ite]
      · simp [coordinatesSame, referenceSame, Ne.symm referenceSame, ite_mul, apply_ite]
    · simp [coordinatesSame, Ne.symm coordinatesSame]

private theorem beforeExponentOperator_readoutEntry (modulus : Nat)
    (problem : KnownOrderProblem E.GroupPoint) (Reference : Register)
    (coordinates prior : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size))
    (branch column : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (reference retained : Reference.Index) :
    (beforeExponentOperator modulus (orderWidth problem) (exponentReadoutCircuit problem)
      Reference)
      (readoutInputBasis modulus (orderWidth problem) Reference ((coordinates, branch), reference))
      (inputLabel modulus.size (2 * orderWidth problem)
        (pairedExponentInput modulus (orderWidth problem) column) prior.1 prior.2, retained) =
      ((if coordinates = prior then 1 else 0) *
        (exponentReadoutCircuit problem).binaryMatrix (prodEquiv branch) (prodEquiv column)) *
          (if reference = retained then 1 else 0) := by
  rw [readoutInputBasis_apply]
  change (beforeExponentProgram modulus (orderWidth problem)
    (exponentReadoutCircuit problem)).matrix
      (inputLabel modulus.size (2 * orderWidth problem)
        (pairedExponentInput modulus (orderWidth problem) branch) coordinates.1 coordinates.2)
      (inputLabel modulus.size (2 * orderWidth problem)
        (pairedExponentInput modulus (orderWidth problem) column) prior.1 prior.2) *
      (if reference = retained then 1 else 0) = _
  rw [beforeExponentProgram_paired_entry]

private theorem idealFourierEventKernel_paired_sum (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (left right : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) :
    idealFourierEventKernel problem event left right =
      ∑ branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem),
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch) =
            true then
          star ((exponentReadoutCircuit problem).binaryMatrix (prodEquiv branch) (prodEquiv left)) *
            (exponentReadoutCircuit problem).binaryMatrix (prodEquiv branch) (prodEquiv right)
          else 0 := by
  unfold idealFourierEventKernel
  exact ((prodEquiv (m := orderWidth problem) (n := orderWidth problem)).sum_comp _).symm.trans
    (Finset.sum_congr rfl fun _ _ => by rw [Equiv.symm_apply_apply])

/-- Actual initialized columns give precisely the original Fourier kernel and retained deltas. -/
theorem afterExponentReadoutEffect_initialized_matrix (modulus : Nat)
    (problem : KnownOrderProblem E.GroupPoint)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register)
    (left right : (idealBranchRegister problem).Index)
    (leftX leftY rightX rightY : Fin (2 ^ modulus.size))
    (leftReference rightReference : Reference.Index) :
    (afterExponentReadoutEffect modulus problem event Reference).matrix
        (initializedOutputEmbedding modulus (2 * orderWidth problem) Reference
          (inputLabel modulus.size (2 * orderWidth problem)
            (pairedExponentInput modulus (orderWidth problem) left) leftX leftY, leftReference))
        (initializedOutputEmbedding modulus (2 * orderWidth problem) Reference
          (inputLabel modulus.size (2 * orderWidth problem)
            (pairedExponentInput modulus (orderWidth problem) right) rightX rightY,
            rightReference)) =
      (if (leftX, leftY) = (rightX, rightY) then 1 else 0) *
        (if leftReference = rightReference then 1 else 0) *
          idealFourierEventKernel problem event left right := by
  rw [idealFourierEventKernel_paired_sum problem event left right,
    afterExponentReadoutEffect_initialized_sum]
  have matching := paired_kernel_sum
    (coordinatesDecision := inferInstance) (referenceDecision := Reference.decEq)
    (readoutInputBasis modulus (orderWidth problem) Reference)
    (fun coordinates branch reference =>
      (inputLabel modulus.size (2 * orderWidth problem)
        (pairedExponentInput modulus (orderWidth problem) branch)
        coordinates.1 coordinates.2, reference))
    (beforeExponentOperator modulus (orderWidth problem) (exponentReadoutCircuit problem)
      Reference)
    (fun output input =>
      (exponentReadoutCircuit problem).binaryMatrix (prodEquiv output) (prodEquiv input))
    (fun output => event fun index => decide
      (((initializedOutputEmbedding modulus (2 * orderWidth problem) Reference output).1
        (afterExponentWires modulus (orderWidth problem) index)).val = 1))
    (fun branch => event
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch))
    (fun coordinates branch reference => by
      rw [readoutInputBasis_apply]
      exact congrArg event (funext fun index =>
        afterExponentWires_initializedValue modulus (orderWidth problem) Reference
          branch coordinates.1 coordinates.2 reference index))
    (fun coordinates branch reference prior column retained =>
      beforeExponentOperator_readoutEntry modulus problem Reference
        coordinates prior branch column reference retained)
    (leftX, leftY) (rightX, rightY) left right leftReference rightReference
  exact matching

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
