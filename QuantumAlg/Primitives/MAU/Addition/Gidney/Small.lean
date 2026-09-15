/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import Mathlib.Tactic.FinCases

/-!
# Zero-, one-, and two-bit pivot flips without helper qubits

These literal X/CNOT lists are derived directly from the pivot-reflection
definition [G17, paper.tex:266-274]. For two target bits, pivot two flips
the low bit under a negative high-bit control, pivot three flips the high
bit under a negative low-bit control, and pivot four complements both.
Pivots zero and one are identity. All finite inputs are proved separately
at these widths. The zero-event identities declare the existing carrier;
every executed gate acts on a target-word wire.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open BinaryLabelEncoding
open EncodedBit.GateSpec
open Nat.FixedWidth

namespace Small

private def declaredProgram {width : Nat}
    (gates : List (EncodedBit.GateSpec (finIdentity width))) : UnitaryCircuit (Qubits width) :=
  (programList gates).seq
    (UnitaryCircuit.identity (Qubits width) (List.range width) List.nodup_range)

private theorem declaredProgram_realizes {width : Nat}
    (gates : List (EncodedBit.GateSpec (finIdentity width))) :
    UnitaryCircuit.Realizes (finIdentity width) (declaredProgram gates) (stepList gates) :=
  (realizesList gates).seq
    (UnitaryCircuit.Realizes.identityAt _ (List.range width) List.nodup_range)

private theorem declaredProgram_physical {width : Nat}
    (gates : List (EncodedBit.GateSpec (finIdentity width))) :
    (declaredProgram gates).physical_idx = List.range width := by
  change (programList gates).physical_idx ∪ List.range width = List.range width
  exact (programList_physical_idx_subset_range gates).union_eq_right

private theorem declaredProgram_eventCost {width : Nat}
    (gates : List (EncodedBit.GateSpec (finIdentity width))) :
    (declaredProgram gates).eventCost = ResourcePool.ofList (gates.map event) := by
  simp only [declaredProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero, programList_eventCost]

private theorem declaredProgram_depth {width : Nat}
    (gates : List (EncodedBit.GateSpec (finIdentity width))) :
    (declaredProgram gates).evaluatedEventDepth (fun _ => 1) = gates.length := by
  rw [declaredProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  change (programList gates).evaluatedEventDepth (fun _ => 1) + 0 = gates.length
  rw [programList_evaluatedEventDepth_unit, Nat.add_zero]

namespace Zero

/-- The unique zero-bit target is fixed for both fitted pivot values. -/
def gates (_pivot : Fin (2 ^ 0 + 1)) : List (EncodedBit.GateSpec (finIdentity 0)) := []

def circuit (pivot : Fin (2 ^ 0 + 1)) : UnitaryCircuit (Qubits 0) :=
  declaredProgram (gates pivot)

theorem gidneySmallZero_step (pivot : Fin (2 ^ 0 + 1)) (input : Fin (2 ^ 0)) :
    stepList (gates pivot) input = pivotWordOutput pivot input := by
  fin_cases pivot <;> fin_cases input <;> rfl

theorem gidneySmallZero_realizes (pivot : Fin (2 ^ 0 + 1)) :
    UnitaryCircuit.Realizes (finIdentity 0) (circuit pivot) (pivotWordOutput pivot) :=
  (declaredProgram_realizes (gates pivot)).congrStep (gidneySmallZero_step pivot)

theorem gidneySmallZero_interface (pivot : Fin (2 ^ 0 + 1)) :
    (circuit pivot).physical_idx = [] ∧ (circuit pivot).eventCost = 0 ∧
      (circuit pivot).evaluatedEventDepth (fun _ => 1) = 0 := by
  exact ⟨declaredProgram_physical (gates pivot),
    declaredProgram_eventCost (gates pivot), declaredProgram_depth (gates pivot)⟩

end Zero

namespace One

private def target : EncodedBit (finIdentity 1) := finIdentityBit 1 0

/-- Only the full-capacity pivot needs a gate: one X on the sole target bit. -/
def gates (pivot : Fin (2 ^ 1 + 1)) : List (EncodedBit.GateSpec (finIdentity 1)) :=
  if pivot.val = 2 then [.x target] else []

def circuit (pivot : Fin (2 ^ 1 + 1)) : UnitaryCircuit (Qubits 1) :=
  declaredProgram (gates pivot)

theorem gidneySmallOne_step (pivot : Fin (2 ^ 1 + 1)) (input : Fin (2 ^ 1)) :
    stepList (gates pivot) input = pivotWordOutput pivot input := by
  fin_cases pivot <;> fin_cases input <;> rfl

theorem gidneySmallOne_realizes (pivot : Fin (2 ^ 1 + 1)) :
    UnitaryCircuit.Realizes (finIdentity 1) (circuit pivot) (pivotWordOutput pivot) :=
  (declaredProgram_realizes (gates pivot)).congrStep (gidneySmallOne_step pivot)

theorem gidneySmallOne_physical (pivot : Fin (2 ^ 1 + 1)) :
    (circuit pivot).physical_idx = List.range 1 :=
  declaredProgram_physical (gates pivot)

/-- The exact native ledger has one X precisely at pivot two. -/
theorem gidneySmallOne_eventCost (pivot : Fin (2 ^ 1 + 1)) :
    (circuit pivot).eventCost = ResourcePool.ofList
      (if pivot.val = 2 then [.gate (.builtin "x")] else []) := by
  rw [circuit, declaredProgram_eventCost]
  fin_cases pivot <;> rfl

theorem gidneySmallOne_depth (pivot : Fin (2 ^ 1 + 1)) :
    (circuit pivot).evaluatedEventDepth (fun _ => 1) =
      if pivot.val = 2 then 1 else 0 := by
  rw [circuit, declaredProgram_depth]
  fin_cases pivot <;> rfl

end One

namespace Two

private def high : EncodedBit (finIdentity 2) := finIdentityBit 2 0
private def low : EncodedBit (finIdentity 2) := finIdentityBit 2 1

/-- Negative controls are explicit surrounding X gates; no helper is allocated. -/
def gates (pivot : Fin (2 ^ 2 + 1)) : List (EncodedBit.GateSpec (finIdentity 2)) :=
  match pivot.val with
  | 2 => [.x high, .cnot high low (by decide), .x high]
  | 3 => [.x low, .cnot low high (by decide), .x low]
  | 4 => [.x high, .x low]
  | _ => []

def circuit (pivot : Fin (2 ^ 2 + 1)) : UnitaryCircuit (Qubits 2) :=
  declaredProgram (gates pivot)

theorem gidneySmallTwo_step (pivot : Fin (2 ^ 2 + 1)) (input : Fin (2 ^ 2)) :
    stepList (gates pivot) input = pivotWordOutput pivot input := by
  fin_cases pivot <;> fin_cases input <;> rfl

theorem gidneySmallTwo_realizes (pivot : Fin (2 ^ 2 + 1)) :
    UnitaryCircuit.Realizes (finIdentity 2) (circuit pivot) (pivotWordOutput pivot) :=
  (declaredProgram_realizes (gates pivot)).congrStep (gidneySmallTwo_step pivot)

theorem gidneySmallTwo_physical (pivot : Fin (2 ^ 2 + 1)) :
    (circuit pivot).physical_idx = List.range 2 :=
  declaredProgram_physical (gates pivot)

/-- Pivots two and three use X/CNOT/X; pivot four uses two X gates. -/
theorem gidneySmallTwo_eventCost (pivot : Fin (2 ^ 2 + 1)) :
    (circuit pivot).eventCost = ResourcePool.ofList
      (if pivot.val = 2 ∨ pivot.val = 3 then
        [.gate (.builtin "x"), .gate (.builtin "cnot"), .gate (.builtin "x")]
      else if pivot.val = 4 then [.gate (.builtin "x"), .gate (.builtin "x")] else []) := by
  rw [circuit, declaredProgram_eventCost]
  fin_cases pivot <;> rfl

theorem gidneySmallTwo_depth (pivot : Fin (2 ^ 2 + 1)) :
    (circuit pivot).evaluatedEventDepth (fun _ => 1) =
      if pivot.val = 2 ∨ pivot.val = 3 then 3 else if pivot.val = 4 then 2 else 0 := by
  rw [circuit, declaredProgram_depth]
  fin_cases pivot <;> rfl

end Two

end Small

end

end QuantumAlg.MAU.Addition.Gidney
