/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Phase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Word

/-!
# Four phase branches sharing each ordinary source occurrence

All four branches execute one common alternating source schedule. Only the
native phase angles are selected, so the number of controlled source calls
does not grow with the common sequence length.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

/-- One ordinary or inverse query preserves both original selectors and the phase ancilla. -/
def signal (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (layout m n) :=
  UnitaryCircuit.onBinarySuffix 1 (Shared.signal (m := m) (n := n) allowControlled inverse)

/-- The four branches have independent phase lists and a single shared source list. -/
def circuit : List ((ℝ × ℝ) × (ℝ × ℝ)) →
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (layout m n)
  | [] => .identity _ _ _
  | angles :: phases =>
      ((circuit phases).seq
        (signal (m := m) (n := n) allowControlled (decide ((phases.length + 1) % 2 = 0)))).seq
        (phase m n positive (UnitarySource.model (m + n) allowControlled true false)
          angles.1.1 angles.1.2 angles.2.1 angles.2.2)

private lemma signal_matrix (inverse : Bool) :
    (((signal (m := m) (n := n) allowControlled inverse).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix ((KnownZero.signal (m := m) (n := n) allowControlled
          inverse).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((KnownZero.signal (m := m) (n := n) allowControlled inverse).binaryMatrix
            (UnitarySource.interpretation U allowControlled true false)))
        (Native.branchMatrix ((KnownZero.signal (m := m) (n := n) allowControlled
          inverse).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((KnownZero.signal (m := m) (n := n) allowControlled inverse).binaryMatrix
            (UnitarySource.interpretation U allowControlled true false))) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix]
  change HilbertOperator.tensor 1 _ = _
  rw [Shared.signal_matrix]
  simp only [Native.branchMatrix_same]

/-- The exact full operator is the four independently specified native source words. -/
lemma fourWord_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (((circuit (m := m) (n := n) positive allowControlled phases).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          ((KnownZero.circuit (m := m) (n := n) positive allowControlled (phases.map fun a
            => a.1.1)).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((KnownZero.circuit (m := m) (n := n) positive allowControlled (phases.map fun a
            => a.1.2)).binaryMatrix (UnitarySource.interpretation U allowControlled true false)))
        (Native.branchMatrix
          ((KnownZero.circuit (m := m) (n := n) positive allowControlled (phases.map fun a
            => a.2.1)).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((KnownZero.circuit (m := m) (n := n) positive allowControlled
            (phases.map fun a => a.2.2)).binaryMatrix
              (UnitarySource.interpretation U allowControlled true false))) := by
  induction phases with
  | nil =>
      simp only [circuit, List.map_nil, KnownZero.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
      change (1 : HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
        Native.branchMatrix (Native.branchMatrix 1 1) (Native.branchMatrix 1 1)
      simp only [Native.branchMatrix_same, HilbertOperator.one_tensor_one]
  | cons angles phases ih =>
      rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
      change _ * (_ * _) = _
      rw [fourPhase_matrix, signal_matrix, ih]
      repeat rw [Native.branchMatrix_mul]
      simp only [List.map_cons, KnownZero.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, List.length_map, Submonoid.coe_mul]

/-- Exact depth retains one query and the complete native phase word for every common slot. -/
lemma fourWord_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (circuit (m := m) (n := n) positive allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 11) * phases.length := by
  induction phases with
  | nil => change 0 = _; simp
  | cons angles phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih, signal,
        UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, Shared.signal_depth,
        fourPhase_depth, List.length_cons]
      ring

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
