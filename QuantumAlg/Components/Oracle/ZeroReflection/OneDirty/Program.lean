/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Coordinates
import all QuantumAlg.Components.Oracle.ZeroReflection.Action
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.FinCases

/-!
# Elementary zero reflection equal to the independent source operator

The literal one-dirty program has full matrix `S0 ⊗ I` in the original
source/work product coordinates. The statement covers both arbitrary work
values and therefore their coherent superpositions and external correlations.
The actual sequence, including complements and the global minus, is retained
when reading its event count.
-/

namespace QuantumAlg.ZeroReflection.OneDirty

noncomputable section

/-- The actual elementary program on the original source followed by its one work wire. -/
def program (controls : Nat) : UnitaryCircuit (Qubits (controls + 1 + 1)) :=
  (layout controls).zeroReflectionProgram

/-- Every source/work basis label has exactly the positive source-reflection phase. -/
theorem program_applyVec_pair (controls : Nat)
    (source : Fin (2 ^ (controls + 1))) (work : Fin (2 ^ 1)) :
    (program controls).applyVec
        (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
          (prodEquiv (source, work))).vec =
      if source = 0 then
        (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
          (prodEquiv (source, work))).vec
      else -(NormalizedVector.ket (R := Qubits (controls + 1 + 1))
        (prodEquiv (source, work))).vec := by
  have encoded :
      (encoding controls).encode (source, finTwoEquiv work) = prodEquiv (source, work) := by
    fin_cases work <;> rfl
  have actual := (layout controls).zeroReflectionProgram_applyVec_encoded_ket
    (source, finTwoEquiv work)
  change (program controls).applyVec
      (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
        ((encoding controls).encode (source, finTwoEquiv work))).vec =
    (if (layout controls).reflectedZero (source, finTwoEquiv work) then
      (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
        ((encoding controls).encode (source, finTwoEquiv work))).vec
    else -(NormalizedVector.ket (R := Qubits (controls + 1 + 1))
      ((encoding controls).encode (source, finTwoEquiv work))).vec) at actual
  simpa only [reflectedZero_iff, encoded] using actual

/-- Full operator equality restores the arbitrary work subsystem, including its correlations. -/
theorem program_matrix (controls : Nat) :
    (program controls).matrix =
      UnitaryOperator.tensor (zeroReflectionOperator (controls + 1))
        (1 : UnitaryOperator (Qubits 1)) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨source, work⟩, rfl⟩ :=
    (prodEquiv (m := controls + 1) (n := 1)).surjective column
  have tensorKet :
      HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (controls + 1)) source).vec
          (NormalizedVector.ket (R := Qubits 1) work).vec =
        (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
          (prodEquiv (source, work))).vec :=
    congrArg NormalizedVector.vec
      (NormalizedVector.tensor_ket (m := controls + 1) (n := 1) source work)
  have expected :
      (UnitaryOperator.tensor (zeroReflectionOperator (controls + 1))
          (1 : UnitaryOperator (Qubits 1))).applyVec
          (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
            (prodEquiv (source, work))).vec =
        if source = 0 then
          (NormalizedVector.ket (R := Qubits (controls + 1 + 1))
            (prodEquiv (source, work))).vec
        else -(NormalizedVector.ket (R := Qubits (controls + 1 + 1))
          (prodEquiv (source, work))).vec := by
    rw [← tensorKet, UnitaryOperator.tensor_applyVec_tensor,
      UnitaryOperator.one_applyVec, zeroReflectionOperator_applyVec_ket]
    by_cases zero : source = 0
    · rw [if_pos zero, if_pos zero]
    · rw [if_neg zero, if_neg zero, HilbertVector.neg_tensor]
  have action := (program_applyVec_pair controls source work).trans expected.symm
  simpa only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    using congrArg (fun state : HilbertVector (Qubits (controls + 1 + 1)) => state row) action

/-- All complement, phase, MCX and exact global-minus events belong to this same program. -/
theorem program_eventTrace_length (controls : Nat) :
    (program controls).eventTrace.length =
      2 * (controls + 1) + (layout controls).gates.length + 6 :=
  (layout controls).zeroReflectionProgram_eventTrace_length

/-- The actual elementary sequence has a linear count with one arbitrary work wire. -/
theorem program_eventTrace_length_le (controls : Nat) :
    (program controls).eventTrace.length ≤ 10 * controls + 9 :=
  (layout controls).zeroReflectionProgram_eventTrace_length_le

end

end QuantumAlg.ZeroReflection.OneDirty
