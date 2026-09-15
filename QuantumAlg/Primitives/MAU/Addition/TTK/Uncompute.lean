/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Readout

/-!
# Correctness of TTK carry uncomputation

The descending sweep extracts a right-word sum XOR before reversing the
operand-encoded carry. The induction preserves the CNOT-before-Toffoli order
inside every source block [TTK09, qic-loglogaddition-quant.tex:303-309,345-349].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec
open Nat.BinaryArithmetic

private def uncomputeSource {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by omega⟩

private def uncomputeTarget {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

private theorem uncomputeSource_ne_target {n : Nat} (i : Fin (n - 1)) :
    uncomputeSource i ≠ uncomputeTarget i := by
  intro h
  have hval := congrArg Fin.val h
  change i.val = i.val + 1 at hval
  omega

private def uncomputeBlock {n : Nat} (i : Fin (n - 1)) :
    List (EncodedBit.GateSpec (encoding n)) :=
  [.cnot (leftBit n (uncomputeTarget i)) (rightBit n (uncomputeTarget i))
     (ttkLeftRight_disjoint n _ _),
   .toffoli (rightBit n (uncomputeSource i)) (leftBit n (uncomputeSource i))
     (leftBit n (uncomputeTarget i))
     (Ne.symm (ttkLeftRight_disjoint n _ _))
     (Ne.symm (ttkLeftRight_disjoint n _ _))
     (ttkLeftLeft_disjoint n _ _ (uncomputeSource_ne_target i))]

private theorem uncomputeBlock_left (n : Nat) (k : Fin (n - 1))
    (i : Fin n) (s : Registers n) :
    (leftBit n i).get (stepList (uncomputeBlock k) s) =
      if i = uncomputeTarget k then
        ((leftBit n i).get s ^^ ((rightBit n (uncomputeSource k)).get s &&
          (leftBit n (uncomputeSource k)).get s))
      else (leftBit n i).get s := by
  change (leftBit n i).get ((EncodedBit.GateSpec.toffoli
    (rightBit n (uncomputeSource k)) (leftBit n (uncomputeSource k))
    (leftBit n (uncomputeTarget k))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (ttkLeftLeft_disjoint n _ _ (uncomputeSource_ne_target k))).step
      ((EncodedBit.GateSpec.cnot (leftBit n (uncomputeTarget k))
        (rightBit n (uncomputeTarget k)) (ttkLeftRight_disjoint n _ _)).step s)) = _
  rw [ttkToffoliRLL_left n (uncomputeSource k) (uncomputeTarget k) i
    (uncomputeSource_ne_target k)]
  simp only [ttkCnotLR_left, ttkCnotLR_right, if_neg (uncomputeSource_ne_target k)]

private theorem uncomputeBlock_right (n : Nat) (k : Fin (n - 1))
    (i : Fin n) (s : Registers n) :
    (rightBit n i).get (stepList (uncomputeBlock k) s) =
      if i = uncomputeTarget k then
        ((rightBit n i).get s ^^ (leftBit n (uncomputeTarget k)).get s)
      else (rightBit n i).get s := by
  change (rightBit n i).get ((EncodedBit.GateSpec.toffoli
    (rightBit n (uncomputeSource k)) (leftBit n (uncomputeSource k))
    (leftBit n (uncomputeTarget k))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (ttkLeftLeft_disjoint n _ _ (uncomputeSource_ne_target k))).step
      ((EncodedBit.GateSpec.cnot (leftBit n (uncomputeTarget k))
        (rightBit n (uncomputeTarget k)) (ttkLeftRight_disjoint n _ _)).step s)) = _
  rw [ttkToffoliRLL_right n (uncomputeSource k) (uncomputeTarget k) i
    (uncomputeSource_ne_target k)]
  exact ttkCnotLR_right n (uncomputeTarget k) (uncomputeTarget k) i s

private def uncomputeInvariant (n : Nat) (original : Registers n)
    (k : Nat) (s : Registers n) : Prop :=
  (∀ i : Fin n, (leftBit n i).get s =
    if i.val ≤ k then
      (original.1.val.testBit i.val ^^ natAddCarry original.1.val original.2.val i.val)
    else if 2 ≤ i.val then
      (original.1.val.testBit i.val ^^ original.1.val.testBit (i.val - 1))
    else original.1.val.testBit i.val) ∧
  (∀ i : Fin n, (rightBit n i).get s =
    if i.val ≤ k then
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)
    else (original.2.val.testBit i.val ^^
      natAddCarry original.1.val original.2.val i.val))

private theorem uncomputeInvariant_left_target (n : Nat) (original s : Registers n)
    (k : Fin (n - 1)) (hs : uncomputeInvariant n original (k.val + 1) s) :
    (leftBit n (uncomputeTarget k)).get (stepList (uncomputeBlock k) s) =
      if 2 ≤ k.val + 1 then
        (original.1.val.testBit (k.val + 1) ^^ original.1.val.testBit k.val)
      else original.1.val.testBit (k.val + 1) := by
  have hle : k.val ≤ k.val + 1 := by omega
  have hsource : (leftBit n (uncomputeSource k)).get s =
      (original.1.val.testBit k.val ^^
        natAddCarry original.1.val original.2.val k.val) := by
    simpa only [uncomputeSource, hle, if_true] using hs.1 (uncomputeSource k)
  have htarget : (leftBit n (uncomputeTarget k)).get s =
      (original.1.val.testBit (k.val + 1) ^^
        natAddCarry original.1.val original.2.val (k.val + 1)) := by
    simpa only [uncomputeTarget, Nat.le_refl, if_true] using hs.1 (uncomputeTarget k)
  have hright : (rightBit n (uncomputeSource k)).get s =
      if k.val = 0 then original.2.val.testBit k.val
      else (original.2.val.testBit k.val ^^ original.1.val.testBit k.val) := by
    have h := hs.2 (uncomputeSource k)
    have hsource_le : (uncomputeSource k).val ≤ k.val + 1 := hle
    rw [if_pos hsource_le] at h
    exact h
  rw [uncomputeBlock_left, if_pos rfl]
  by_cases hk : k.val = 0
  · have hlow : ¬ 2 ≤ k.val + 1 := by omega
    rw [if_neg hlow, htarget, hright, hsource]
    simp only [hk, natAddCarry, Bool.xor_false]
    cases original.1.val.testBit 0 <;> cases original.2.val.testBit 0 <;> simp [Bool.carry]
  · have hhigh : 2 ≤ k.val + 1 := by omega
    rw [if_pos hhigh]
    rw [if_neg hk] at hright
    have h := ttkCarryGate_reverse_target
      (rightBit n (uncomputeSource k)) (leftBit n (uncomputeSource k))
      (leftBit n (uncomputeTarget k))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (ttkLeftLeft_disjoint n _ _ (uncomputeSource_ne_target k)) s
      (original.1.val.testBit k.val) (original.2.val.testBit k.val)
      (natAddCarry original.1.val original.2.val k.val)
      (original.1.val.testBit (k.val + 1)) hright hsource
      (by simpa only [natAddCarry] using htarget)
    change (leftBit n (uncomputeTarget k)).get (EncodedBit.toffoliStep
      (rightBit n (uncomputeSource k)) (leftBit n (uncomputeSource k))
      (leftBit n (uncomputeTarget k)) s) = _ at h
    rw [EncodedBit.toffoliStep_get_target] at h
    exact h

private theorem uncomputeInvariant_right_target (n : Nat) (original s : Registers n)
    (k : Fin (n - 1)) (hs : uncomputeInvariant n original (k.val + 1) s) :
    (rightBit n (uncomputeTarget k)).get (stepList (uncomputeBlock k) s) =
      (original.2.val.testBit (k.val + 1) ^^
        natAddCarry original.1.val original.2.val (k.val + 1)) := by
  have hleft : (leftBit n (uncomputeTarget k)).get s =
      (original.1.val.testBit (k.val + 1) ^^
        natAddCarry original.1.val original.2.val (k.val + 1)) := by
    simpa only [uncomputeTarget, Nat.le_refl, if_true] using hs.1 (uncomputeTarget k)
  have hright : (rightBit n (uncomputeTarget k)).get s =
      (original.2.val.testBit (k.val + 1) ^^ original.1.val.testBit (k.val + 1)) := by
    simpa only [uncomputeTarget, Nat.le_refl, if_true, Nat.succ_ne_zero, if_false]
      using hs.2 (uncomputeTarget k)
  rw [uncomputeBlock_right, if_pos rfl]
  have h := ttkSumExtraction_target
    (leftBit n (uncomputeTarget k)) (rightBit n (uncomputeTarget k))
    (ttkLeftRight_disjoint n _ _) s
    (original.1.val.testBit (k.val + 1)) (original.2.val.testBit (k.val + 1))
    (natAddCarry original.1.val original.2.val (k.val + 1)) hleft hright
  change (rightBit n (uncomputeTarget k)).get (EncodedBit.cnotStep
    (leftBit n (uncomputeTarget k)) (rightBit n (uncomputeTarget k)) s) = _ at h
  rw [EncodedBit.cnotStep_get_target] at h
  exact h

private theorem uncomputeInvariant_step (n : Nat) (original s : Registers n)
    (k : Fin (n - 1)) (hs : uncomputeInvariant n original (k.val + 1) s) :
    uncomputeInvariant n original k.val (stepList (uncomputeBlock k) s) := by
  constructor
  · intro i
    by_cases hi : i = uncomputeTarget k
    · subst i
      have hnle : ¬ (uncomputeTarget k).val ≤ k.val := by
        change ¬ k.val + 1 ≤ k.val
        omega
      rw [if_neg hnle]
      simpa only [uncomputeTarget, Nat.add_sub_cancel]
        using uncomputeInvariant_left_target n original s k hs
    · rw [uncomputeBlock_left, if_neg hi, hs.1 i]
      have hival : i.val ≠ k.val + 1 := by
        intro h
        exact hi (Fin.ext h)
      by_cases hle : i.val ≤ k.val
      · have hle' : i.val ≤ k.val + 1 := by omega
        rw [if_pos hle, if_pos hle']
      · have hle' : ¬ i.val ≤ k.val + 1 := by omega
        rw [if_neg hle, if_neg hle']
  · intro i
    by_cases hi : i = uncomputeTarget k
    · subst i
      have hnle : ¬ (uncomputeTarget k).val ≤ k.val := by
        change ¬ k.val + 1 ≤ k.val
        omega
      rw [if_neg hnle]
      exact uncomputeInvariant_right_target n original s k hs
    · rw [uncomputeBlock_right, if_neg hi, hs.2 i]
      have hival : i.val ≠ k.val + 1 := by
        intro h
        exact hi (Fin.ext h)
      by_cases hle : i.val ≤ k.val
      · have hle' : i.val ≤ k.val + 1 := by omega
        rw [if_pos hle, if_pos hle']
      · have hle' : ¬ i.val ≤ k.val + 1 := by omega
        rw [if_neg hle, if_neg hle']

/-- Stage four restores the adjacent addend XORs and extracts every sum-carry XOR. -/
theorem ttkUncomputeSweep (n : Nat) (original s : Registers n)
    (hleft : ∀ i : Fin n, (leftBit n i).get s =
      (original.1.val.testBit i.val ^^
        natAddCarry original.1.val original.2.val i.val))
    (hright : ∀ i : Fin n, (rightBit n i).get s =
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)) :
    (∀ i : Fin n, (leftBit n i).get (stepList (descendingUncomputeGates n) s) =
      if 2 ≤ i.val then
        (original.1.val.testBit i.val ^^ original.1.val.testBit (i.val - 1))
      else original.1.val.testBit i.val) ∧
    (∀ i : Fin n, (rightBit n i).get (stepList (descendingUncomputeGates n) s) =
      (original.2.val.testBit i.val ^^
        natAddCarry original.1.val original.2.val i.val)) := by
  have hstart : uncomputeInvariant n original (n - 1) s := by
    constructor
    · intro i
      have hle : i.val ≤ n - 1 := by omega
      simpa only [if_pos hle] using hleft i
    · intro i
      have hle : i.val ≤ n - 1 := by omega
      simpa only [if_pos hle] using hright i
  have h := ttkDescendingBlockInduction (uncomputeBlock (n := n))
    (uncomputeInvariant n original) s hstart
    (fun k state hs => uncomputeInvariant_step n original state k hs)
  change uncomputeInvariant n original 0
    (stepList (descendingUncomputeGates n) s) at h
  constructor
  · intro i
    by_cases hi : i.val = 0
    · simpa [hi, natAddCarry] using h.1 i
    · have hile : ¬ i.val ≤ 0 := by omega
      simpa only [if_neg hile] using h.1 i
  · intro i
    by_cases hi : i.val = 0
    · simpa [hi, natAddCarry] using h.2 i
    · have hile : ¬ i.val ≤ 0 := by omega
      simpa only [if_neg hile] using h.2 i

end

end QuantumAlg.MAU.Addition.TTK
