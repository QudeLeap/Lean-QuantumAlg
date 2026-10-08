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
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Gate.Basic
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
def program (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (layout controls).zeroReflectionProgram physical oracles

/-- Every source/work basis label has exactly the positive source-reflection phase. -/
theorem program_applyVec_pair (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1))
    (source : Fin (2 ^ (controls + 1))) (work : Fin (2 ^ 1)) :
    (program oracles controls physical).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (prodEquiv (source, work)))).vec =
      if source = 0 then
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (prodEquiv (source, work)))).vec
      else -(NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (prodEquiv (source, work)))).vec := by
  have encoded :
      (encoding controls).encode (source, finTwoEquiv work) = prodEquiv (source, work) := by
    fin_cases work <;> rfl
  have actual := (layout controls).zeroReflectionProgram_applyVec_encoded_ket physical oracles
    (source, finTwoEquiv work)
  change (program oracles controls physical).applyVec
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm
          ((encoding controls).encode (source, finTwoEquiv work)))).vec =
    (if (layout controls).reflectedZero (source, finTwoEquiv work) then
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm
          ((encoding controls).encode (source, finTwoEquiv work)))).vec
    else -(NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm
          ((encoding controls).encode (source, finTwoEquiv work)))).vec) at actual
  simpa only [reflectedZero_iff, encoded] using actual

/-- Full operator equality restores the arbitrary work subsystem, including its correlations. -/
theorem program_matrix (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) :
    UnitaryOperator.reindex physical.basisEquiv (program oracles controls physical).matrix =
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
  have actual := congrArg (fun state => state (physical.basisEquiv.symm row))
    (program_applyVec_pair oracles controls physical source work)
  have sourceEntry := congrArg (fun state => state row) expected
  simp only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket] at actual
  simp only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at sourceEntry
  by_cases zero : source = 0
  · rw [if_pos zero] at actual sourceEntry
    change (program oracles controls physical).matrix (physical.basisEquiv.symm row)
        (physical.basisEquiv.symm (prodEquiv (source, work))) =
      ((NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (prodEquiv (source, work))))
        (physical.basisEquiv.symm row)) at actual
    change (UnitaryOperator.tensor (zeroReflectionOperator (controls + 1))
        (1 : UnitaryOperator (Qubits 1))) row (prodEquiv (source, work)) =
      ((NormalizedVector.ket (prodEquiv (source, work))) row) at sourceEntry
    rw [NormalizedVector.ket_apply] at actual sourceEntry
    simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply] at actual
    exact actual.trans sourceEntry.symm
  · rw [if_neg zero] at actual sourceEntry
    change (program oracles controls physical).matrix (physical.basisEquiv.symm row)
        (physical.basisEquiv.symm (prodEquiv (source, work))) =
      -((NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (prodEquiv (source, work))))
        (physical.basisEquiv.symm row)) at actual
    change (UnitaryOperator.tensor (zeroReflectionOperator (controls + 1))
        (1 : UnitaryOperator (Qubits 1))) row (prodEquiv (source, work)) =
      -((NormalizedVector.ket (prodEquiv (source, work))) row) at sourceEntry
    rw [NormalizedVector.ket_apply] at actual sourceEntry
    simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply] at actual
    exact actual.trans sourceEntry.symm

/-- All complement, phase, MCX and exact global-minus events belong to this same program. -/
theorem program_eventTrace_length (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) :
    (program oracles controls physical).eventTrace.length =
      2 * (controls + 1) + (layout controls).gates.length + 3 :=
  (layout controls).zeroReflectionProgram_eventTrace_length physical oracles

/-- The actual elementary sequence has a linear count with one arbitrary work wire. -/
theorem program_eventTrace_length_le (oracles : OracleModel) (controls : Nat)
    (physical : QubitLayout (controls + 1 + 1)) :
    (program oracles controls physical).eventTrace.length ≤ 10 * controls + 6 :=
  (layout controls).zeroReflectionProgram_eventTrace_length_le physical oracles

end

end QuantumAlg.ZeroReflection.OneDirty
