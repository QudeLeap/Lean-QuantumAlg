/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Word

/-!
# A common source sequence with coherently selected phases

Every slot issues one ordinary or inverse source query, shared by both
selector branches. Only the phase angles depend on the selector. The complete
matrix is the direct sum of the two source words, without controlled source
calls [GSLW19, BlockHam.tex:883-890].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

/-- One shared query leaves both selector and phase ancilla untouched. -/
def signal (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U allowControlled true false)
      (layout m n) :=
  UnitaryCircuit.onBinarySuffix 1 (KnownZero.signal U allowControlled inverse)

/-- Both selector branches contain the same single physical source query. -/
theorem signal_matrix (inverse : Bool) :
    ((signal U allowControlled inverse).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (m + n))))) =
      Native.branchMatrix (KnownZero.signal U allowControlled inverse).binaryMatrix
        (KnownZero.signal U allowControlled inverse).binaryMatrix := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    Native.branchMatrix_same]
  rfl

/-- Equal-length branch phases share one alternating sequence of source accesses. -/
def circuit : List (ℝ × ℝ) →
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U allowControlled true false)
      (layout m n)
  | [] => .identity _ _ _
  | angles :: phases =>
      ((circuit phases).seq
        (signal U allowControlled (decide ((phases.length + 1) % 2 = 0)))).seq
        (phase m n positive (UnitarySource.model U allowControlled true false) angles.1 angles.2)

/-- The actual shared word equals the direct sum of both independently specified branch words. -/
theorem circuit_matrix (phases : List (ℝ × ℝ)) :
    ((circuit U positive allowControlled phases).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (m + n))))) =
      Native.branchMatrix
        (KnownZero.circuit U positive allowControlled (phases.map Prod.fst)).binaryMatrix
        (KnownZero.circuit U positive allowControlled (phases.map Prod.snd)).binaryMatrix := by
  induction phases with
  | nil =>
      simp only [circuit, List.map_nil, KnownZero.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
      rw [Native.branchMatrix_same]
      exact HilbertOperator.one_tensor_one.symm
  | cons angles phases ih =>
      rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
      change _ * (_ * _) = _
      rw [phase_matrix, signal_matrix, ih, Native.branchMatrix_mul, Native.branchMatrix_mul]
      simp only [List.map_cons, KnownZero.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, List.length_map, Submonoid.coe_mul]

/-- One shared source occurrence contributes one abstract dependency step. -/
theorem signal_depth (inverse : Bool) :
    (signal U allowControlled inverse).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, KnownZero.signal_depth]

/-- Exact depth counts one source query, two native flips and four selector gates per slot. -/
theorem circuit_depth (phases : List (ℝ × ℝ)) :
    (circuit U positive allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 5) * phases.length := by
  induction phases with
  | nil => change 0 = _; simp
  | cons angles phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih, signal_depth, phase_depth,
        List.length_cons]
      ring

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
