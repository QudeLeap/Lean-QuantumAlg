/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Word

/-!
# Four phase branches sharing each ordinary source occurrence

All four branches execute one common alternating source schedule. Only the
native phase angles are selected, so the number of controlled source calls
does not grow with the common sequence length.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (allowControlled : Bool)

/-- The four branches have independent phase lists and a single shared source list. -/
def circuit : List ((ℝ × ℝ) × (ℝ × ℝ)) →
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (SharedFour.layout m n)
  | [] => .identity _ _ _
  | angles :: phases =>
      ((circuit phases).seq
        (SharedFour.signal (m := m) (n := n) allowControlled (decide ((phases.length + 1) % 2
          = 0)))).seq
        (phase m n (UnitarySource.model (m + n) allowControlled true false)
          angles.1.1 angles.1.2 angles.2.1 angles.2.2)

/-- The exact full operator is the four independently specified native source words. -/
lemma totalFourWord_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (((circuit (m := m) (n := n) allowControlled phases).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) :
      HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          ((Total.circuit (m := m) (n := n) allowControlled (phases.map fun a
            => a.1.1)).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((Total.circuit (m := m) (n := n) allowControlled (phases.map fun a
            => a.1.2)).binaryMatrix (UnitarySource.interpretation U allowControlled true false)))
        (Native.branchMatrix
          ((Total.circuit (m := m) (n := n) allowControlled (phases.map fun a
            => a.2.1)).binaryMatrix (UnitarySource.interpretation U allowControlled true false))
          ((Total.circuit (m := m) (n := n) allowControlled
            (phases.map fun a => a.2.2)).binaryMatrix
              (UnitarySource.interpretation U allowControlled true false))) := by
  induction phases with
  | nil =>
      simp only [circuit, List.map_nil, Total.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
      change (1 : HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
        Native.branchMatrix (Native.branchMatrix 1 1) (Native.branchMatrix 1 1)
      simp only [Native.branchMatrix_same, HilbertOperator.one_tensor_one]
  | cons angles phases ih =>
      rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
      change _ * (_ * _) = _
      rw [totalFourPhase_matrix, SharedFour.signal_matrix, ih]
      repeat rw [Native.branchMatrix_mul]
      simp only [List.map_cons, Total.circuit,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, List.length_map, Submonoid.coe_mul]

/-- Exact depth retains one query and the complete native phase word for every common slot. -/
lemma totalFourWord_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (circuit (m := m) (n := n) allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (phaseDepth m n + 1) * phases.length := by
  induction phases with
  | nil => change 0 = _; simp
  | cons angles phases ih =>
      simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, ih, SharedFour.signal,
        UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth, Shared.signal_depth,
        totalFourPhase_depth, List.length_cons]
      ring

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
