/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Readout

/-!
# Correctness of the TTK carry sweep

Each increasing Toffoli replaces an adjacent input XOR by an input-carry XOR.
The low step uses the original low operand bits and no carry-in wire. Carries
are the existing natural-number addition carry sequence
[TTK09, qic-loglogaddition-quant.tex:262-283,298-302,337-345].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec
open Nat.BinaryArithmetic

private def carrySource {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by omega⟩

private def carryTarget {n : Nat} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

private theorem carrySource_ne_target {n : Nat} (i : Fin (n - 1)) :
    carrySource i ≠ carryTarget i := by
  intro h
  have hval := congrArg Fin.val h
  change i.val = i.val + 1 at hval
  omega

private def carrySweepGate {n : Nat} (i : Fin (n - 1)) :
    EncodedBit.GateSpec (encoding n) :=
  .toffoli (rightBit n (carrySource i)) (leftBit n (carrySource i))
    (leftBit n (carryTarget i))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (Ne.symm (ttkLeftRight_disjoint n _ _))
    (ttkLeftLeft_disjoint n _ _ (carrySource_ne_target i))

private def carryInvariant (n : Nat) (original : Registers n)
    (k : Nat) (s : Registers n) : Prop :=
  (∀ i : Fin n, (leftBit n i).get s =
    if i.val ≤ k then
      (original.1.val.testBit i.val ^^ natAddCarry original.1.val original.2.val i.val)
    else if 2 ≤ i.val then
      (original.1.val.testBit i.val ^^ original.1.val.testBit (i.val - 1))
    else original.1.val.testBit i.val) ∧
  (∀ i : Fin n, (rightBit n i).get s =
    if i.val = 0 then original.2.val.testBit i.val
    else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val))

private theorem carryInvariant_target (n : Nat) (original s : Registers n)
    (k : Fin (n - 1)) (hs : carryInvariant n original k.val s) :
    (leftBit n (carryTarget k)).get ((carrySweepGate k).step s) =
      (original.1.val.testBit (k.val + 1) ^^
        natAddCarry original.1.val original.2.val (k.val + 1)) := by
  have hsource : (leftBit n (carrySource k)).get s =
      (original.1.val.testBit k.val ^^
        natAddCarry original.1.val original.2.val k.val) := by
    simpa only [carrySource, Nat.le_refl, if_true] using hs.1 (carrySource k)
  have hnle : ¬ k.val + 1 ≤ k.val := by omega
  have htarget : (leftBit n (carryTarget k)).get s =
      if 2 ≤ k.val + 1 then
        (original.1.val.testBit (k.val + 1) ^^ original.1.val.testBit k.val)
      else original.1.val.testBit (k.val + 1) := by
    simpa only [carryTarget, if_neg hnle, Nat.add_sub_cancel]
      using hs.1 (carryTarget k)
  have hright : (rightBit n (carrySource k)).get s =
      if k.val = 0 then original.2.val.testBit k.val
      else (original.2.val.testBit k.val ^^ original.1.val.testBit k.val) :=
    hs.2 (carrySource k)
  by_cases hk : k.val = 0
  · have hlow : ¬ 2 ≤ k.val + 1 := by omega
    rw [if_neg hlow] at htarget
    rw [if_pos hk] at hright
    have hsource' : (leftBit n (carrySource k)).get s =
        original.1.val.testBit k.val := by
      simpa only [hk, natAddCarry, Bool.xor_false] using hsource
    change (leftBit n (carryTarget k)).get (EncodedBit.toffoliStep
      (rightBit n (carrySource k)) (leftBit n (carrySource k))
      (leftBit n (carryTarget k)) s) = _
    rw [EncodedBit.toffoliStep_get_target, htarget, hright, hsource']
    simp only [hk, natAddCarry]
    cases original.1.val.testBit 0 <;> cases original.2.val.testBit 0 <;> rfl
  · have hhigh : 2 ≤ k.val + 1 := by omega
    rw [if_pos hhigh] at htarget
    rw [if_neg hk] at hright
    have h := ttkCarryGate_target
      (rightBit n (carrySource k)) (leftBit n (carrySource k))
      (leftBit n (carryTarget k))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (ttkLeftLeft_disjoint n _ _ (carrySource_ne_target k)) s
      (original.1.val.testBit k.val) (original.2.val.testBit k.val)
      (natAddCarry original.1.val original.2.val k.val)
      (original.1.val.testBit (k.val + 1)) hright hsource htarget
    simpa only [carryGate, carrySweepGate, carrySource, carryTarget, natAddCarry] using h

private theorem carryInvariant_step (n : Nat) (original s : Registers n)
    (k : Fin (n - 1)) (hs : carryInvariant n original k.val s) :
    carryInvariant n original (k.val + 1) ((carrySweepGate k).step s) := by
  constructor
  · intro i
    by_cases hi : i = carryTarget k
    · subst i
      have hle : (carryTarget k).val ≤ k.val + 1 := Nat.le_refl _
      rw [if_pos hle]
      exact carryInvariant_target n original s k hs
    · change (leftBit n i).get ((EncodedBit.GateSpec.toffoli
        (rightBit n (carrySource k)) (leftBit n (carrySource k))
        (leftBit n (carryTarget k))
        (Ne.symm (ttkLeftRight_disjoint n _ _))
        (Ne.symm (ttkLeftRight_disjoint n _ _))
        (ttkLeftLeft_disjoint n _ _ (carrySource_ne_target k))).step s) = _
      rw [ttkToffoliRLL_left n (carrySource k) (carryTarget k) i
        (carrySource_ne_target k), if_neg hi, hs.1 i]
      have hival : i.val ≠ k.val + 1 := by
        intro h
        exact hi (Fin.ext h)
      by_cases hle : i.val ≤ k.val
      · have hle' : i.val ≤ k.val + 1 := by omega
        rw [if_pos hle, if_pos hle']
      · have hle' : ¬ i.val ≤ k.val + 1 := by omega
        rw [if_neg hle, if_neg hle']
  · intro i
    change (rightBit n i).get ((EncodedBit.GateSpec.toffoli
      (rightBit n (carrySource k)) (leftBit n (carrySource k))
      (leftBit n (carryTarget k))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (Ne.symm (ttkLeftRight_disjoint n _ _))
      (ttkLeftLeft_disjoint n _ _ (carrySource_ne_target k))).step s) = _
    rw [ttkToffoliRLL_right n (carrySource k) (carryTarget k) i (carrySource_ne_target k)]
    exact hs.2 i

/-- Stage three stores each canonical incoming carry in its addend bit.
The right operand retains the stage-one XOR pattern. -/
theorem ttkCarrySweep (n : Nat) (original s : Registers n)
    (hleft : ∀ i : Fin n, (leftBit n i).get s =
      if 2 ≤ i.val then
        (original.1.val.testBit i.val ^^ original.1.val.testBit (i.val - 1))
      else original.1.val.testBit i.val)
    (hright : ∀ i : Fin n, (rightBit n i).get s =
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)) :
    (∀ i : Fin n, (leftBit n i).get (stepList (carryGates n) s) =
      (original.1.val.testBit i.val ^^
        natAddCarry original.1.val original.2.val i.val)) ∧
    (∀ i : Fin n, (rightBit n i).get (stepList (carryGates n) s) =
      if i.val = 0 then original.2.val.testBit i.val
      else (original.2.val.testBit i.val ^^ original.1.val.testBit i.val)) := by
  have hstart : carryInvariant n original 0 s := by
    constructor
    · intro i
      by_cases hi : i.val = 0
      · simpa [hi, natAddCarry] using hleft i
      · have hile : ¬ i.val ≤ 0 := by omega
        simpa only [if_neg hile] using hleft i
    · exact hright
  have h := ttkAscendingGateInduction (carrySweepGate (n := n))
    (carryInvariant n original) s hstart
    (fun k state hs => carryInvariant_step n original state k hs)
  change carryInvariant n original (n - 1) (stepList (carryGates n) s) at h
  constructor
  · intro i
    have hle : i.val ≤ n - 1 := by omega
    simpa only [if_pos hle] using h.1 i
  · exact h.2

end

end QuantumAlg.MAU.Addition.TTK
