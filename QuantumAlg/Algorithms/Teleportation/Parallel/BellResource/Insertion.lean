/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Core.Base.State.Density.PureMarginal

/-!
# Complete input-reference slices under the local Bell promise

Only the supplied Bell subsystem is promised locally pure [dW19,
qcnotes.tex:785,809]. Positivity then factors the entire joint input and
external-reference matrix through a rectangular Bell insertion. The unknown
input may be entangled across blocks and with the reference. This is a
mathematical coordinate identity, not a preparation operation or an additional
reference-dependent admission condition.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.BellInsertion

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Rectangular insertion along declared coordinates; this is not an execution operation. -/
def insertAlong {A B S : Type} (coordinates : S ≃ A × B) (resource : B → ℂ) :
    Matrix S A ℂ := fun row input =>
  if (coordinates row).1 = input then resource (coordinates row).2 else 0

/-- A pure resource factor gives the complete matrix, with no restriction on the input matrix. -/
lemma insertAlong_sandwich_entry {A B S : Type} [Fintype A]
    (coordinates : S ≃ A × B) (resource : B → ℂ) (input : Matrix A A ℂ)
    (row column : S) :
    (insertAlong coordinates resource * input *
      (insertAlong coordinates resource).conjTranspose) row column =
        (resource (coordinates row).2 * star (resource (coordinates column).2)) *
          input (coordinates row).1 (coordinates column).1 := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, insertAlong, apply_ite]
  ring

/-- Insert the supplied bank into its original physical resource wires. -/
def physicalInsertion (count : Nat) :
    Matrix (context count).register.Index (inputRegister count).Index ℂ :=
  insertAlong (inputBellBasis count) (bellBank count)

/-- A full original input/reference slice, tracing only the original shared Bell resource. -/
def inputReferenceSlice (count : Nat) {Reference : Register}
    (state : DensityOperator ((context count).register.prod Reference))
    (leftRef rightRef : Reference.Index) : HilbertOperator (inputRegister count) :=
  fun row column => ∑ resource : (bellRegister count).Index,
    state.matrix ((inputBellBasis count).symm (row, resource), leftRef)
      ((inputBellBasis count).symm (column, resource), rightRef)

/-- The local pure Bell promise alone factors every arbitrary external-reference slice. -/
lemma original_slice_eq_insertion (count : Nat) {Reference : Register}
    (state : DensityOperator ((context count).register.prod Reference))
    (promised : localBellMarginal count state.marginalLeft =
      DensityOperator.ofPure (bellBank count))
    (leftRef rightRef : Reference.Index) :
    state.matrix.submatrix (fun index => (index, leftRef))
      (fun index => (index, rightRef)) =
      physicalInsertion count * inputReferenceSlice count state leftRef rightRef *
        (physicalInsertion count).conjTranspose := by
  ext row column
  have factor := bellResource_joint_entry count Reference state promised
    (inputBellBasis count row).1 (inputBellBasis count column).1
    (inputBellBasis count row).2 (inputBellBasis count column).2 leftRef rightRef
  have original : state.matrix (row, leftRef) (column, rightRef) =
      (bellBank count (inputBellBasis count row).2 *
        star (bellBank count (inputBellBasis count column).2)) *
        inputReferenceSlice count state leftRef rightRef
          (inputBellBasis count row).1 (inputBellBasis count column).1 := by
    simpa only [Prod.mk.eta, Equiv.symm_apply_apply, inputReferenceSlice] using factor
  exact original.trans (insertAlong_sandwich_entry (inputBellBasis count) (bellBank count)
    (inputReferenceSlice count state leftRef rightRef) row column).symm

/-- Any actual full branch can now be composed with Bell insertion before acting on the input. -/
lemma conjugation_eq_inserted (count : Nat) {Reference : Register}
    (state : DensityOperator ((context count).register.prod Reference))
    (promised : localBellMarginal count state.marginalLeft =
      DensityOperator.ofPure (bellBank count))
    (operator : HilbertOperator (context count).register)
    (leftRef rightRef : Reference.Index) :
    operator * state.matrix.submatrix (fun index => (index, leftRef))
      (fun index => (index, rightRef)) * operator.conjTranspose =
      (operator * physicalInsertion count) * inputReferenceSlice count state leftRef rightRef *
        (operator * physicalInsertion count).conjTranspose := by
  rw [original_slice_eq_insertion count state promised leftRef rightRef]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.QuantumTeleportation.Parallel.BellInsertion
