/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Target.Coordinates
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument.Physical
import all QuantumAlg.Algorithms.Teleportation.Parallel.Channel.Retained
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates.Projector
import all QuantumAlg.Core.Execution.Reference.Preparation

/-!
# Retained physical insertion realizes the independently specified full target

The selector adjoints retain both measured Alice systems and the original
Bob system. Their tensor product is the coordinate insertion of the actual
stored Alice label, with identity on the arbitrary joint input. The resulting
matrix sandwich preserves every external-reference entry.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.Target

noncomputable section

open Execution MeasurementInstrument PhysicalInstrument PhysicalNative
open RetainedSource ProjectorCoordinates BellInsertion
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma storedAliceLabel (count : Nat) (stored : Store (context count))
    (block : Fin count) :
    outcomeValue (storedBits (stored.read (resultInput count)) block).1
      (storedBits (stored.read (resultInput count)) block).2 =
        aliceLabel (stored.read (resultInput count)) block :=
  stored_outcome_label count stored block

private lemma selector_adjoint_entry (label : Fin 4) (row : Fin 8) (column : Fin 2) :
    (selector label).conjTranspose row column =
      if ((prodEquiv (m := 2) (n := 1)).symm row).1 = label ∧
          ((prodEquiv (m := 2) (n := 1)).symm row).2 = column then 1 else 0 := by
  simp only [selector, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, selectHead]
  change star (if label = ((prodEquiv (m := 2) (n := 1)).symm row).1 then
    if column = ((prodEquiv (m := 2) (n := 1)).symm row).2 then (1 : ℂ) else 0 else 0) = _
  simp only [(eq_comm : label = ((prodEquiv (m := 2) (n := 1)).symm row).1 ↔ _),
    (eq_comm : column = ((prodEquiv (m := 2) (n := 1)).symm row).2 ↔ _)]
  by_cases head : ((prodEquiv (m := 2) (n := 1)).symm row).1 = label <;>
    by_cases tail : ((prodEquiv (m := 2) (n := 1)).symm row).2 = column <;>
      simp [head, tail]

/-- The existing retained branch operator uses the target's independent
physical coordinates. -/
lemma retainedPhysicalInsertion_eq_insertAlong (count : Nat)
    (stored : Store (context count)) :
    retainedPhysicalInsertion count stored =
      insertAlong ((outputBasis count).trans (Equiv.prodComm _ _))
        (NormalizedVector.ket (R := bellRegister count)
          (aliceLabel (stored.read (resultInput count)))) := by
  ext row column
  obtain ⟨labels, rfl⟩ := (contextBankBasis count).symm.surjective row
  let head : (bellRegister count).Index :=
    fun block => ((prodEquiv (m := 2) (n := 1)).symm (labels block)).1
  let tail : (inputRegister count).Index :=
    fun block => ((prodEquiv (m := 2) (n := 1)).symm (labels block)).2
  let label := aliceLabel (stored.read (resultInput count))
  have physical : retainedPhysicalInsertion count stored
      ((contextBankBasis count).symm labels) column =
        ∏ block : Fin count,
          if head block = label block ∧ tail block = column block then (1 : ℂ) else 0 := by
    simp only [retainedPhysicalInsertion, tensorEntries, Equiv.apply_symm_apply]
    apply Finset.prod_congr rfl
    intro block _
    rw [selector_adjoint_entry, storedAliceLabel]
  rw [physical]
  simp only [insertAlong, outputBasis_native, Equiv.trans_apply,
    NormalizedVector.ket_apply]
  change (∏ block : Fin count,
      if head block = label block ∧ tail block = column block then (1 : ℂ) else 0) =
    if tail = column then if head = label then 1 else 0 else 0
  by_cases sameHead : head = label
  · by_cases sameTail : tail = column
    · rw [if_pos sameTail, if_pos sameHead]
      apply Finset.prod_eq_one
      intro block _
      exact if_pos ⟨congrFun sameHead block, congrFun sameTail block⟩
    · rw [if_neg sameTail]
      have different : ∃ block, tail block ≠ column block := by
        by_contra none
        exact sameTail (funext fun block => not_not.mp (fun bad => none ⟨block, bad⟩))
      obtain ⟨block, different⟩ := different
      exact Finset.prod_eq_zero (Finset.mem_univ block)
        (if_neg (fun both => different both.2))
  · have absent : (if tail = column then if head = label then (1 : ℂ) else 0 else 0) = 0 := by
      simp only [if_neg sameHead, ite_self]
    rw [absent]
    have different : ∃ block, head block ≠ label block := by
      by_contra none
      exact sameHead (funext fun block => not_not.mp (fun bad => none ⟨block, bad⟩))
    obtain ⟨block, different⟩ := different
    exact Finset.prod_eq_zero (Finset.mem_univ block)
      (if_neg (fun both => different both.1))

private lemma target_entry (count : Nat) {Reference : Register}
    (input : Input (context count) Reference) (value : CShape.Value (resultShape count))
    (row column : (context count).register.Index) (leftRef rightRef : Reference.Index) :
    (target count input value).matrix (row, leftRef) (column, rightRef) =
      (NormalizedVector.ket (R := bellRegister count) (aliceLabel value)
          (outputBasis count row).1 *
        star (NormalizedVector.ket (R := bellRegister count) (aliceLabel value)
          (outputBasis count column).1)) *
        (originalInput count input).matrix
          ((outputBasis count row).2, leftRef) ((outputBasis count column).2, rightRef) := by
  rfl

/-- Reinserting the actual Alice label retains the full original input/reference density on Bob. -/
lemma retained_sandwich_target_entry (count : Nat) {Reference : Register}
    (input : Input (context count) Reference) (stored : Store (context count))
    (row column : (context count).register.Index) (leftRef rightRef : Reference.Index) :
    (retainedPhysicalInsertion count stored *
        inputReferenceSlice count input.state.quantumMarginal leftRef rightRef *
        (retainedPhysicalInsertion count stored).conjTranspose) row column =
      (target count input (stored.read (resultInput count))).matrix
        (row, leftRef) (column, rightRef) := by
  rw [retainedPhysicalInsertion_eq_insertAlong, insertAlong_sandwich_entry,
    target_entry, originalInput_entry]
  rfl

end

end QuantumAlg.QuantumTeleportation.Parallel.Target
