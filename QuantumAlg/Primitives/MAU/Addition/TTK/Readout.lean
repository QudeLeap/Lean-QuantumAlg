/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Gates
import all QuantumAlg.Primitives.MAU.Addition.TTK.LocalAction
import Mathlib.Data.List.OfFn

/-!
# Readout proofs for TTK sweeps

These proof lemmas inspect the existing gate lists and operand bit lenses.
The increasing and decreasing induction principles follow the source's loop
orders [TTK09, qic-loglogaddition-quant.tex:290-318].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

/-- Induction through a finite increasing sequence of actual gates. -/
lemma ttkAscendingGateInduction {Data : Type} {E : BinaryLabelEncoding Data}
    {m : Nat} (gate : Fin m → EncodedBit.GateSpec E) (P : Nat → Data → Prop)
    (state : Data) (hzero : P 0 state)
    (hstep : ∀ (i : Fin m) (s : Data), P i.val s → P (i.val + 1) ((gate i).step s)) :
    P m (stepList (List.ofFn gate) state) := by
  induction m generalizing state with
  | zero => simpa only [List.ofFn_zero, stepList, id_eq] using hzero
  | succ m ih =>
      rw [List.ofFn_succ', List.concat_eq_append, stepList_append]
      change P (m + 1) ((gate (Fin.last m)).step
        (stepList (List.ofFn fun i : Fin m => gate i.castSucc) state))
      apply hstep (Fin.last m)
      exact ih (fun i => gate i.castSucc) state hzero
        (fun i s hs => hstep i.castSucc s hs)

/-- Induction through a finite decreasing sequence of actual gates. -/
lemma ttkDescendingGateInduction {Data : Type} {E : BinaryLabelEncoding Data}
    {m : Nat} (gate : Fin m → EncodedBit.GateSpec E) (P : Nat → Data → Prop)
    (state : Data) (hstart : P m state)
    (hstep : ∀ (i : Fin m) (s : Data), P (i.val + 1) s → P i.val ((gate i).step s)) :
    P 0 (stepList (List.ofFn gate).reverse state) := by
  induction m generalizing state with
  | zero => simpa only [List.ofFn_zero, List.reverse_nil, stepList, id_eq] using hstart
  | succ m ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
      change P 0 (stepList (List.ofFn fun i : Fin m => gate i.castSucc).reverse
        ((gate (Fin.last m)).step state))
      exact ih (fun i => gate i.castSucc) ((gate (Fin.last m)).step state)
        (hstep (Fin.last m) state hstart)
        (fun i s hs => hstep i.castSucc s hs)

/-- Descending block induction preserves the order of gates inside each block. -/
lemma ttkDescendingBlockInduction {Data : Type} {E : BinaryLabelEncoding Data}
    {m : Nat} (block : Fin m → List (EncodedBit.GateSpec E)) (P : Nat → Data → Prop)
    (state : Data) (hstart : P m state)
    (hstep : ∀ (i : Fin m) (s : Data),
      P (i.val + 1) s → P i.val (stepList (block i) s)) :
    P 0 (stepList (List.ofFn block).reverse.flatten state) := by
  induction m generalizing state with
  | zero =>
      simpa only [List.ofFn_zero, List.reverse_nil, List.flatten_nil, stepList, id_eq]
        using hstart
  | succ m ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat,
        List.flatten_cons, stepList_append]
      exact ih (fun i => block i.castSucc) (stepList (block (Fin.last m)) state)
        (hstep (Fin.last m) state hstart)
        (fun i s hs => hstep i.castSucc s hs)

/-- A bounded predecessor index; its zero case is never read as a predecessor. -/
def previousBit {n : Nat} (i : Fin n) : Fin n :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- A left-to-right CNOT preserves every addend bit. -/
lemma ttkCnotLR_left (n : Nat) (a b i : Fin n) (s : Registers n) :
    (leftBit n i).get ((EncodedBit.GateSpec.cnot (leftBit n a) (rightBit n b)
      (ttkLeftRight_disjoint n a b)).step s) = (leftBit n i).get s :=
  EncodedBit.cnotStep_get_of_target_ne _ _ _
    (Ne.symm (ttkLeftRight_disjoint n i b)) s

/-- A left-to-right CNOT updates exactly its addressed target bit. -/
lemma ttkCnotLR_right (n : Nat) (a b i : Fin n) (s : Registers n) :
    (rightBit n i).get ((EncodedBit.GateSpec.cnot (leftBit n a) (rightBit n b)
      (ttkLeftRight_disjoint n a b)).step s) =
      if i = b then ((rightBit n i).get s ^^ (leftBit n a).get s)
      else (rightBit n i).get s := by
  by_cases h : i = b
  · subst i
    rw [if_pos rfl]
    exact EncodedBit.cnotStep_get_target (leftBit n a) (rightBit n b) s
  · rw [if_neg h]
    exact EncodedBit.cnotStep_get_of_target_ne _ _ _
      (ttkRightRight_disjoint n b i (Ne.symm h)) s

/-- An operand-internal CNOT updates exactly its addressed addend bit. -/
lemma ttkCnotLL_left (n : Nat) (a b i : Fin n) (hab : a ≠ b) (s : Registers n) :
    (leftBit n i).get ((EncodedBit.GateSpec.cnot (leftBit n a) (leftBit n b)
      (ttkLeftLeft_disjoint n a b hab)).step s) =
      if i = b then ((leftBit n i).get s ^^ (leftBit n a).get s)
      else (leftBit n i).get s := by
  by_cases h : i = b
  · subst i
    rw [if_pos rfl]
    exact EncodedBit.cnotStep_get_target (leftBit n a) (leftBit n b) s
  · rw [if_neg h]
    exact EncodedBit.cnotStep_get_of_target_ne _ _ _
      (ttkLeftLeft_disjoint n b i (Ne.symm h)) s

/-- An operand-internal CNOT preserves every right operand bit. -/
lemma ttkCnotLL_right (n : Nat) (a b i : Fin n) (hab : a ≠ b) (s : Registers n) :
    (rightBit n i).get ((EncodedBit.GateSpec.cnot (leftBit n a) (leftBit n b)
      (ttkLeftLeft_disjoint n a b hab)).step s) = (rightBit n i).get s :=
  EncodedBit.cnotStep_get_of_target_ne _ _ _ (ttkLeftRight_disjoint n b i) s

/-- A TTK carry Toffoli updates exactly its addressed operand bit. -/
lemma ttkToffoliRLL_left (n : Nat) (a b i : Fin n) (hab : a ≠ b) (s : Registers n) :
    (leftBit n i).get ((EncodedBit.GateSpec.toffoli
      (rightBit n a) (leftBit n a) (leftBit n b)
      (Ne.symm (ttkLeftRight_disjoint n a a))
      (Ne.symm (ttkLeftRight_disjoint n b a))
      (ttkLeftLeft_disjoint n a b hab)).step s) =
      if i = b then ((leftBit n i).get s ^^
        ((rightBit n a).get s && (leftBit n a).get s))
      else (leftBit n i).get s := by
  by_cases h : i = b
  · subst i
    rw [if_pos rfl]
    exact EncodedBit.toffoliStep_get_target (rightBit n a) (leftBit n a) (leftBit n b) s
  · rw [if_neg h]
    exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (ttkLeftLeft_disjoint n b i (Ne.symm h)) s

/-- A TTK carry Toffoli preserves every right operand bit. -/
lemma ttkToffoliRLL_right (n : Nat) (a b i : Fin n) (hab : a ≠ b) (s : Registers n) :
    (rightBit n i).get ((EncodedBit.GateSpec.toffoli
      (rightBit n a) (leftBit n a) (leftBit n b)
      (Ne.symm (ttkLeftRight_disjoint n a a))
      (Ne.symm (ttkLeftRight_disjoint n b a))
      (ttkLeftLeft_disjoint n a b hab)).step s) = (rightBit n i).get s :=
  EncodedBit.toffoliStep_get_of_target_ne _ _ _ _ (ttkLeftRight_disjoint n b i) s

end

end QuantumAlg.MAU.Addition.TTK
