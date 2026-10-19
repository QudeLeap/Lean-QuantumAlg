/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Readout

/-!
# Correctness of the operand XOR chain

The descending sweep stores adjacent input XORs in the addend. After carry
uncomputation, the increasing sweep restores those same bits. These proofs
follow the actual gate order for every width, without a carry workspace
[TTK09, qic-loglogaddition-quant.tex:295-298,311-314,330-352].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

private def chainSource {n : Nat} (i : Fin (n - 2)) : Fin n :=
  ⟨i.val + 1, by omega⟩

private def chainTarget {n : Nat} (i : Fin (n - 2)) : Fin n :=
  ⟨i.val + 2, by omega⟩

private lemma chainSource_ne_target {n : Nat} (i : Fin (n - 2)) :
    chainSource i ≠ chainTarget i := by
  intro h
  have hval := congrArg Fin.val h
  change i.val + 1 = i.val + 2 at hval
  omega

private lemma previousBit_chainTarget {n : Nat} (i : Fin (n - 2)) :
    previousBit (chainTarget i) = chainSource i := by
  apply Fin.ext
  change i.val + 2 - 1 = i.val + 1
  omega

private def chainGate {n : Nat} (i : Fin (n - 2)) : EncodedBit.GateSpec (encoding n) :=
  .cnot (leftBit n (chainSource i)) (leftBit n (chainTarget i))
    (ttkLeftLeft_disjoint n _ _ (chainSource_ne_target i))

private def chainInvariant (n : Nat) (original rightState : Registers n)
    (k : Nat) (s : Registers n) : Prop :=
  (∀ i : Fin n, (leftBit n i).get s =
    if k + 2 ≤ i.val then
      ((leftBit n i).get original ^^ (leftBit n (previousBit i)).get original)
    else (leftBit n i).get original) ∧
  (∀ i : Fin n, (rightBit n i).get s = (rightBit n i).get rightState)

private lemma chainInvariant_descending_step (n : Nat)
    (original rightState s : Registers n) (k : Fin (n - 2))
    (hs : chainInvariant n original rightState (k.val + 1) s) :
    chainInvariant n original rightState k.val ((chainGate k).step s) := by
  constructor
  · intro i
    change (leftBit n i).get ((EncodedBit.GateSpec.cnot
      (leftBit n (chainSource k)) (leftBit n (chainTarget k))
      (ttkLeftLeft_disjoint n _ _ (chainSource_ne_target k))).step s) = _
    rw [ttkCnotLL_left n (chainSource k) (chainTarget k) i (chainSource_ne_target k)]
    by_cases hi : i = chainTarget k
    · subst i
      rw [if_pos rfl, hs.1 (chainTarget k), hs.1 (chainSource k)]
      have ht : ¬ k.val + 1 + 2 ≤ (chainTarget k).val := by
        change ¬ k.val + 1 + 2 ≤ k.val + 2
        omega
      have ha : ¬ k.val + 1 + 2 ≤ (chainSource k).val := by
        change ¬ k.val + 1 + 2 ≤ k.val + 1
        omega
      have hb : k.val + 2 ≤ (chainTarget k).val := Nat.le_refl _
      rw [if_neg ht, if_neg ha, if_pos hb, previousBit_chainTarget]
    · rw [if_neg hi, hs.1 i]
      have hival : i.val ≠ k.val + 2 := by
        intro h
        exact hi (Fin.ext h)
      by_cases hle : k.val + 2 ≤ i.val
      · have hle' : k.val + 1 + 2 ≤ i.val := by omega
        rw [if_pos hle, if_pos hle']
      · have hle' : ¬ k.val + 1 + 2 ≤ i.val := by omega
        rw [if_neg hle, if_neg hle']
  · intro i
    change (rightBit n i).get ((EncodedBit.GateSpec.cnot
      (leftBit n (chainSource k)) (leftBit n (chainTarget k))
      (ttkLeftLeft_disjoint n _ _ (chainSource_ne_target k))).step s) = _
    rw [ttkCnotLL_right n (chainSource k) (chainTarget k) i (chainSource_ne_target k)]
    exact hs.2 i

private lemma chainInvariant_ascending_step (n : Nat)
    (original rightState s : Registers n) (k : Fin (n - 2))
    (hs : chainInvariant n original rightState k.val s) :
    chainInvariant n original rightState (k.val + 1) ((chainGate k).step s) := by
  constructor
  · intro i
    change (leftBit n i).get ((EncodedBit.GateSpec.cnot
      (leftBit n (chainSource k)) (leftBit n (chainTarget k))
      (ttkLeftLeft_disjoint n _ _ (chainSource_ne_target k))).step s) = _
    rw [ttkCnotLL_left n (chainSource k) (chainTarget k) i (chainSource_ne_target k)]
    by_cases hi : i = chainTarget k
    · subst i
      rw [if_pos rfl, hs.1 (chainTarget k), hs.1 (chainSource k)]
      have ht : k.val + 2 ≤ (chainTarget k).val := Nat.le_refl _
      have ha : ¬ k.val + 2 ≤ (chainSource k).val := by
        change ¬ k.val + 2 ≤ k.val + 1
        omega
      have hb : ¬ k.val + 1 + 2 ≤ (chainTarget k).val := by
        change ¬ k.val + 1 + 2 ≤ k.val + 2
        omega
      rw [if_pos ht, if_neg ha, if_neg hb, previousBit_chainTarget]
      simp
    · rw [if_neg hi, hs.1 i]
      have hival : i.val ≠ k.val + 2 := by
        intro h
        exact hi (Fin.ext h)
      by_cases hle : k.val + 2 ≤ i.val
      · have hle' : k.val + 1 + 2 ≤ i.val := by omega
        rw [if_pos hle, if_pos hle']
      · have hle' : ¬ k.val + 1 + 2 ≤ i.val := by omega
        rw [if_neg hle, if_neg hle']
  · intro i
    change (rightBit n i).get ((EncodedBit.GateSpec.cnot
      (leftBit n (chainSource k)) (leftBit n (chainTarget k))
      (ttkLeftLeft_disjoint n _ _ (chainSource_ne_target k))).step s) = _
    rw [ttkCnotLL_right n (chainSource k) (chainTarget k) i (chainSource_ne_target k)]
    exact hs.2 i

/-- Stage two writes adjacent addend XORs above bit one and preserves the target. -/
lemma ttkDescendingXor (n : Nat) (s : Registers n) :
    (∀ i : Fin n, (leftBit n i).get (stepList (descendingXorGates n) s) =
      if 2 ≤ i.val then
        ((leftBit n i).get s ^^ (leftBit n (previousBit i)).get s)
      else (leftBit n i).get s) ∧
    (∀ i : Fin n, (rightBit n i).get (stepList (descendingXorGates n) s) =
      (rightBit n i).get s) := by
  have hstart : chainInvariant n s s (n - 2) s := by
    constructor
    · intro i
      have hi : ¬ n - 2 + 2 ≤ i.val := by omega
      rw [if_neg hi]
    · intro i
      rfl
  have h := ttkDescendingGateInduction chainGate (chainInvariant n s s) s hstart
    (fun k state hs => chainInvariant_descending_step n s s state k hs)
  change chainInvariant n s s 0 (stepList (descendingXorGates n) s) at h
  exact h

/-- Stage five restores any addend with the adjacent-XOR pattern left by stage four.
The right operand is arbitrary and all of its bits are preserved. -/
lemma ttkAscendingXor (n : Nat) (original s : Registers n)
    (hleft : ∀ i : Fin n, (leftBit n i).get s =
      if 2 ≤ i.val then
        ((leftBit n i).get original ^^ (leftBit n (previousBit i)).get original)
      else (leftBit n i).get original) :
    (∀ i : Fin n, (leftBit n i).get (stepList (ascendingXorGates n) s) =
      (leftBit n i).get original) ∧
    (∀ i : Fin n, (rightBit n i).get (stepList (ascendingXorGates n) s) =
      (rightBit n i).get s) := by
  have hstart : chainInvariant n original s 0 s := ⟨hleft, fun _ => rfl⟩
  have h := ttkAscendingGateInduction chainGate (chainInvariant n original s) s hstart
    (fun k state hs => chainInvariant_ascending_step n original s state k hs)
  have hgates : ascendingXorGates n = List.ofFn (chainGate (n := n)) := by
    simp only [ascendingXorGates, descendingXorGates, List.reverse_reverse]
    rfl
  rw [← hgates] at h
  constructor
  · intro i
    have hi : ¬ n - 2 + 2 ≤ i.val := by omega
    simpa only [if_neg hi] using h.1 i
  · exact h.2

end

end QuantumAlg.MAU.Addition.TTK
