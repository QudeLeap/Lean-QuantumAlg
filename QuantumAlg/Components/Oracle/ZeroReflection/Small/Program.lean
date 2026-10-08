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
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Gate.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Canonical small-width elementary source reflection without a work register

Widths zero through three use their actual zero, one, two or three source
wires. The complete matrix is the independent positive source reflection;
the actual event counts are respectively zero, one, five and ten.
-/

namespace QuantumAlg.ZeroReflection.Small

open BinaryLabelEncoding

noncomputable section

/-- Select only the literal work-free construction at each small source width. -/
def program (oracles : OracleModel) : (width : Nat) → (physical : QubitLayout width) →
    width ≤ 3 → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | 0, physical, _ => UnitaryCircuit.identity AlgorithmGate.model oracles physical.toQuantum
  | 1, physical, _ => (finIdentityBit 1 0).pauliZ physical oracles
  | 2, physical, _ => (finIdentityBit 2 0).twoWireZeroReflection physical oracles
      (finIdentityBit 2 1) (by decide)
  | 3, physical, _ => (finIdentityBit 3 0).threeWireZeroReflection physical oracles
      (finIdentityBit 3 1) (finIdentityBit 3 2) (by decide) (by decide) (by decide)
  | _ + 4, _, small => False.elim (by omega)

/-- Every complete basis label has precisely the independent source-reflection phase. -/
theorem program_applyVec_ket (oracles : OracleModel) (width : Nat) (physical : QubitLayout width)
    (small : width ≤ 3) (label : Fin (2 ^ width)) :
    (program oracles width physical small).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec =
      if label = 0 then (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec := by
  interval_cases width
  · have zero : label = 0 := Fin.ext (by omega)
    simp [program, UnitaryCircuit.applyVec, UnitaryCircuit.identity_matrix,
      UnitaryOperator.one_applyVec, zero]
  · have zeroIff : (finIdentityBit 1 0).get label = false ↔ label = 0 := by
      rw [← finIdentity_all_zero_iff 1 label]
      exact ⟨fun head index => by fin_cases index; exact head, fun allBits => allBits 0⟩
    have actual := (finIdentityBit 1 0).pauliZ_reflects_zero physical oracles label
    change (program oracles 1 physical small).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec =
      (if (finIdentityBit 1 0).get label = false then
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec) at actual
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
    have actual := (finIdentityBit 2 0).twoWireZeroReflection_applyVec_encoded_ket physical oracles
      (finIdentityBit 2 1) (by decide) label
    change (program oracles 2 physical small).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec =
      (if (finIdentityBit 2 0).get label = false ∧ (finIdentityBit 2 1).get label = false then
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec) at actual
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
      physical oracles
      (finIdentityBit 3 1) (finIdentityBit 3 2) (by decide) (by decide) (by decide) label
    change (program oracles 3 physical small).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec =
      (if ((finIdentityBit 3 0).get label = false ∧ (finIdentityBit 3 1).get label = false) ∧
        (finIdentityBit 3 2).get label = false then
          (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm label)).vec) at actual
    simpa only [zeroIff] using actual

/-- Full matrix equality holds with exactly the original source width and no work factor. -/
theorem program_matrix (oracles : OracleModel) (width : Nat) (physical : QubitLayout width)
    (small : width ≤ 3) :
    UnitaryOperator.reindex physical.basisEquiv (program oracles width physical small).matrix =
      zeroReflectionOperator width := by
  apply Subtype.ext
  ext row column
  have actual := congrArg (fun state => state (physical.basisEquiv.symm row))
    (program_applyVec_ket oracles width physical small column)
  have expected := congrArg (fun state => state row)
    (zeroReflectionOperator_applyVec_ket width column)
  simp only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket] at actual
  simp only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at expected
  by_cases zero : column = 0
  · rw [if_pos zero] at actual expected
    change (program oracles width physical small).matrix (physical.basisEquiv.symm row)
        (physical.basisEquiv.symm (column)) =
      ((NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (column))) (physical.basisEquiv.symm row)) at actual
    change (zeroReflectionOperator width) row (column) =
      ((NormalizedVector.ket (column)) row) at expected
    rw [NormalizedVector.ket_apply] at actual expected
    simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply] at actual
    exact actual.trans expected.symm
  · rw [if_neg zero] at actual expected
    change (program oracles width physical small).matrix (physical.basisEquiv.symm row)
        (physical.basisEquiv.symm (column)) =
      -((NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (column))) (physical.basisEquiv.symm row)) at actual
    change (zeroReflectionOperator width) row (column) =
      -((NormalizedVector.ket (column)) row) at expected
    rw [NormalizedVector.ket_apply] at actual expected
    simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply] at actual
    exact actual.trans expected.symm

/-- The exact event count is read from the literal construction in each small-width branch. -/
theorem program_eventTrace_length (oracles : OracleModel) (width : Nat)
    (physical : QubitLayout width)
    (small : width ≤ 3) :
    (program oracles width physical small).eventTrace.length =
      match width with | 0 => 0 | 1 => 1 | 2 => 5 | _ => 10 := by
  interval_cases width <;>
    simp only [program, UnitaryCircuit.identity_eventTrace, List.length_nil,
      EncodedBit.pauliZ_eventTrace, List.length_singleton,
      EncodedBit.twoWireZeroReflection_eventTrace_length,
      EncodedBit.threeWireZeroReflection_eventTrace_length]

end

end QuantumAlg.ZeroReflection.Small
