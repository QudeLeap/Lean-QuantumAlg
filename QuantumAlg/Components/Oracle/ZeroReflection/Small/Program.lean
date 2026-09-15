/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Action
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Small.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.ZeroReadout
import all QuantumAlg.Core.Base.UnitaryCircuit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Canonical small-width elementary source reflection without a work register

Widths zero through three use their actual zero, one, two or three source
wires. The complete matrix is the independent positive source reflection;
the actual event counts are respectively zero, one, five and thirteen.
-/

namespace QuantumAlg.ZeroReflection.Small

open BinaryLabelEncoding

noncomputable section

/-- Select only the literal work-free construction at each small source width. -/
def program : (width : Nat) → width ≤ 3 → UnitaryCircuit (Qubits width)
  | 0, _ => UnitaryCircuit.identity (Qubits 0) [] (by simp)
  | 1, _ => (finIdentityBit 1 0).pauliZ
  | 2, _ => (finIdentityBit 2 0).twoWireZeroReflection (finIdentityBit 2 1) (by decide)
  | 3, _ => (finIdentityBit 3 0).threeWireZeroReflection
      (finIdentityBit 3 1) (finIdentityBit 3 2) (by decide) (by decide) (by decide)
  | _ + 4, small => False.elim (by omega)

/-- Every complete basis label has precisely the independent source-reflection phase. -/
theorem program_applyVec_ket (width : Nat) (small : width ≤ 3) (label : Fin (2 ^ width)) :
    (program width small).applyVec (NormalizedVector.ket (R := Qubits width) label).vec =
      if label = 0 then (NormalizedVector.ket (R := Qubits width) label).vec
      else -(NormalizedVector.ket (R := Qubits width) label).vec := by
  interval_cases width
  · have zero : label = 0 := Fin.ext (by omega)
    simp [program, UnitaryCircuit.applyVec_identity, zero]
  · have zeroIff : (finIdentityBit 1 0).get label = false ↔ label = 0 := by
      rw [← finIdentity_all_zero_iff 1 label]
      exact ⟨fun head index => by fin_cases index; exact head, fun allBits => allBits 0⟩
    have actual := (finIdentityBit 1 0).pauliZ_reflects_zero label
    change (program 1 small).applyVec (NormalizedVector.ket (R := Qubits 1) label).vec =
      (if (finIdentityBit 1 0).get label = false then
        (NormalizedVector.ket (R := Qubits 1) label).vec
      else -(NormalizedVector.ket (R := Qubits 1) label).vec) at actual
    simpa only [zeroIff] using actual
  · have zeroIff :
        ((finIdentityBit 2 0).get label = false ∧ (finIdentityBit 2 1).get label = false) ↔
          label = 0 := by
      rw [← finIdentity_all_zero_iff 2 label]
      constructor
      · rintro ⟨first, second⟩ index
        fin_cases index <;> assumption
      · intro allBits
        exact ⟨allBits 0, allBits 1⟩
    have actual := (finIdentityBit 2 0).twoWireZeroReflection_applyVec_encoded_ket
      (finIdentityBit 2 1) (by decide) label
    change (program 2 small).applyVec (NormalizedVector.ket (R := Qubits 2) label).vec =
      (if (finIdentityBit 2 0).get label = false ∧ (finIdentityBit 2 1).get label = false then
        (NormalizedVector.ket (R := Qubits 2) label).vec
      else -(NormalizedVector.ket (R := Qubits 2) label).vec) at actual
    simpa only [zeroIff] using actual
  · have zeroIff :
        (((finIdentityBit 3 0).get label = false ∧ (finIdentityBit 3 1).get label = false) ∧
          (finIdentityBit 3 2).get label = false) ↔ label = 0 := by
      rw [← finIdentity_all_zero_iff 3 label]
      constructor
      · rintro ⟨⟨first, second⟩, third⟩ index
        fin_cases index <;> assumption
      · intro allBits
        exact ⟨⟨allBits 0, allBits 1⟩, allBits 2⟩
    have actual := (finIdentityBit 3 0).threeWireZeroReflection_applyVec_encoded_ket
      (finIdentityBit 3 1) (finIdentityBit 3 2) (by decide) (by decide) (by decide) label
    change (program 3 small).applyVec (NormalizedVector.ket (R := Qubits 3) label).vec =
      (if ((finIdentityBit 3 0).get label = false ∧ (finIdentityBit 3 1).get label = false) ∧
        (finIdentityBit 3 2).get label = false then
          (NormalizedVector.ket (R := Qubits 3) label).vec
      else -(NormalizedVector.ket (R := Qubits 3) label).vec) at actual
    simpa only [zeroIff] using actual

/-- Full matrix equality holds with exactly the original source width and no work factor. -/
theorem program_matrix (width : Nat) (small : width ≤ 3) :
    (program width small).matrix = zeroReflectionOperator width := by
  apply Subtype.ext
  ext row column
  have action := (program_applyVec_ket width small column).trans
    (zeroReflectionOperator_applyVec_ket width column).symm
  simpa only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    using congrArg (fun state : HilbertVector (Qubits width) => state row) action

/-- The exact event count is read from the literal construction in each small-width branch. -/
theorem program_eventTrace_length (width : Nat) (small : width ≤ 3) :
    (program width small).eventTrace.length =
      match width with | 0 => 0 | 1 => 1 | 2 => 5 | _ => 13 := by
  interval_cases width <;>
    simp only [program, UnitaryCircuit.identity_eventTrace, List.length_nil,
      EncodedBit.pauliZ_eventTrace, List.length_singleton,
      EncodedBit.twoWireZeroReflection_eventTrace_length,
      EncodedBit.threeWireZeroReflection_eventTrace_length]

end

end QuantumAlg.ZeroReflection.Small
