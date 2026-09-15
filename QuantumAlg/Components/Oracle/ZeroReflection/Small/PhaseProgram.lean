/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Small.ControlledZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Small.Phase
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.ZeroReadout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Small source reflection controlled by an original phase position

Zero, one or two source wires require no work position. The original phase
control acts through the literal identity, H/CNOT/H, or eight-gate controlled
two-wire reflection. All other original phase values remain unchanged.
-/

namespace QuantumAlg.ZeroReflection.SmallPhase

open BinaryLabelEncoding PhaseWorkspace

noncomputable section

private theorem source_two_ne (phases : Nat) :
    (sourceBit phases 1 0).wire ≠ (sourceBit phases 1 1).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding phases 1).width => wire.val) same
  change phases + 0 = phases + 1 at values
  omega

/-- The small-width branch uses only the selected existing control and original source wires. -/
def program (phases : Nat) :
    (width : Nat) → width ≤ 2 → Fin phases → UnitaryCircuit (Qubits (phases + width))
  | 0, _, _ => UnitaryCircuit.identity (Qubits (phases + 0))
      (List.range phases) List.nodup_range
  | 1, _, control => (phaseBit phases 0 control).controlledZ
      (sourceBit phases 0 0) (phaseBit_ne_sourceBit phases 0 control 0)
  | 2, _, control => (phaseBit phases 1 control).controlledTwoWireZeroReflection
      (sourceBit phases 1 0) (sourceBit phases 1 1)
      (phaseBit_ne_sourceBit phases 1 control 0) (phaseBit_ne_sourceBit phases 1 control 1)
      (source_two_ne phases)
  | _ + 3, small, _ => False.elim (by omega)

/-- The full phase/source label has the original controlled positive source-reflection phase. -/
theorem program_applyVec_pair (phases width : Nat) (small : width ≤ 2)
    (control : Fin phases) (phase : Fin (2 ^ phases)) (source : Fin (2 ^ width)) :
    (program phases width small control).applyVec
        (NormalizedVector.ket (R := Qubits (phases + width)) (prodEquiv (phase, source))).vec =
      if (finIdentityBit phases control).get phase then
        if source = 0 then
          (NormalizedVector.ket (R := Qubits (phases + width)) (prodEquiv (phase, source))).vec
        else -(NormalizedVector.ket (R := Qubits (phases + width)) (prodEquiv (phase, source))).vec
      else (NormalizedVector.ket (R := Qubits (phases + width))
        (prodEquiv (phase, source))).vec := by
  interval_cases width
  · have zero : source = 0 := Fin.ext (by omega)
    simp [program, UnitaryCircuit.applyVec_identity, zero]
  · have zeroIff : (finIdentityBit 1 0).get source = false ↔ source = 0 := by
      rw [← finIdentity_all_zero_iff 1 source]
      exact ⟨fun head index => by fin_cases index; exact head, fun allBits => allBits 0⟩
    have actual := (phaseBit phases 0 control).controlledZ_reflects_zero
      (sourceBit phases 0 0) (phaseBit_ne_sourceBit phases 0 control 0) (phase, source)
    change (program phases 1 small control).applyVec
        (NormalizedVector.ket (R := Qubits (phases + 1)) (prodEquiv (phase, source))).vec =
      (if (phaseBit phases 0 control).get (phase, source) then
        if (sourceBit phases 0 0).get (phase, source) = false then
          (NormalizedVector.ket (R := Qubits (phases + 1)) (prodEquiv (phase, source))).vec
        else -(NormalizedVector.ket (R := Qubits (phases + 1)) (prodEquiv (phase, source))).vec
      else (NormalizedVector.ket (R := Qubits (phases + 1))
        (prodEquiv (phase, source))).vec) at actual
    simpa only [phaseBit_get, sourceBit_get, zeroIff] using actual
  · have zeroIff :
        ((finIdentityBit 2 0).get source = false ∧ (finIdentityBit 2 1).get source = false) ↔
          source = 0 := by
      rw [← finIdentity_all_zero_iff 2 source]
      constructor
      · rintro ⟨first, second⟩ index
        fin_cases index <;> assumption
      · intro allBits
        exact ⟨allBits 0, allBits 1⟩
    have actual := (phaseBit phases 1 control).controlledTwoWireZeroReflection_applyVec_encoded_ket
      (sourceBit phases 1 0) (sourceBit phases 1 1)
      (phaseBit_ne_sourceBit phases 1 control 0) (phaseBit_ne_sourceBit phases 1 control 1)
      (source_two_ne phases) (phase, source)
    change (program phases 2 small control).applyVec
        (NormalizedVector.ket (R := Qubits (phases + 2)) (prodEquiv (phase, source))).vec =
      (if (phaseBit phases 1 control).get (phase, source) then
        if (sourceBit phases 1 0).get (phase, source) = false ∧
          (sourceBit phases 1 1).get (phase, source) = false then
          (NormalizedVector.ket (R := Qubits (phases + 2)) (prodEquiv (phase, source))).vec
        else -(NormalizedVector.ket (R := Qubits (phases + 2)) (prodEquiv (phase, source))).vec
      else (NormalizedVector.ket (R := Qubits (phases + 2))
        (prodEquiv (phase, source))).vec) at actual
    simpa only [phaseBit_get, sourceBit_get, zeroIff] using actual

/-- The same small-width programs contain exactly zero, three or eight actual events. -/
theorem program_eventTrace_length (phases width : Nat) (small : width ≤ 2)
    (control : Fin phases) :
    (program phases width small control).eventTrace.length =
      match width with | 0 => 0 | 1 => 3 | _ => 8 := by
  interval_cases width
  · rfl
  · exact (phaseBit phases 0 control).controlledZ_eventTrace_length
      (sourceBit phases 0 0) (phaseBit_ne_sourceBit phases 0 control 0)
  · exact (phaseBit phases 1 control).controlledTwoWireZeroReflection_eventTrace_length
      (sourceBit phases 1 0) (sourceBit phases 1 1)
      (phaseBit_ne_sourceBit phases 1 control 0) (phaseBit_ne_sourceBit phases 1 control 1)
      (source_two_ne phases)

end

end QuantumAlg.ZeroReflection.SmallPhase
