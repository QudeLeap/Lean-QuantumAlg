/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Bell measurement: a random marginal with a perfectly correlated joint result

These are Born probabilities of the actual Bell vector prepared by
`BellStatePreparation.circuit`. Measuring its first wire alone gives a fair
bit. Measuring both wires gives only `00` or `11`, each with the same mass
[dW19, qcnotes.tex:622,5409,5420].
-/

namespace QuantumAlg.BellStatePreparation.Measurement

noncomputable section

def qubitLayout : QubitLayout 2 where
  physical_idx := ![0, 1]
  physical_idx_injective := by decide

def placedBell : QubitLayout.State qubitLayout where
  state := PureState.ofNormalized bell qubitLayout.systemIdx
  system_idx_eq := rfl

def firstZ : TerminalZMeasure qubitLayout 1 :=
  zMeasureAt qubitLayout ![0] (by decide)

def bothZ : TerminalZMeasure qubitLayout 2 :=
  zMeasure qubitLayout

private lemma firstZeroFiber :
    Finset.univ.filter (fun basis : Fin (2 ^ 2) =>
      firstZ.readout basis = ![false]) = {0, 1} := by
  decide

private lemma firstOneFiber :
    Finset.univ.filter (fun basis : Fin (2 ^ 2) =>
      firstZ.readout basis = ![true]) = {2, 3} := by
  decide

private lemma bothZeroFiber :
    Finset.univ.filter (fun basis : Fin (2 ^ 2) =>
      bothZ.readout basis = ![false, false]) = {0} := by
  decide

private lemma bothOneFiber :
    Finset.univ.filter (fun basis : Fin (2 ^ 2) =>
      bothZ.readout basis = ![true, true]) = {3} := by
  decide

private lemma bothMismatchFiber :
    Finset.univ.filter (fun basis : Fin (2 ^ 2) =>
      bothZ.readout basis = ![false, true]) = {1} := by
  decide

private lemma invSqrt2_enorm_sq :
    ‖NormalizedVector.invSqrt2‖ₑ ^ 2 = (2 : ENNReal)⁻¹ := by
  calc
    ‖NormalizedVector.invSqrt2‖ₑ ^ 2 =
        ENNReal.ofReal ‖NormalizedVector.invSqrt2‖ ^ 2 :=
      congrArg (fun value : ENNReal => value ^ 2)
        (ofReal_norm NormalizedVector.invSqrt2).symm
    _ = ENNReal.ofReal (‖NormalizedVector.invSqrt2‖ ^ 2) :=
      (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    _ = (2 : ENNReal)⁻¹ := by
      rw [NormalizedVector.norm_sq_invSqrt2]
      simp

/-- The first Bell wire has a fair zero outcome, despite the joint correlation. -/
lemma first_zero_probability :
    firstZ.outcomePMF placedBell ![false] = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply, firstZeroFiber]
  simp [placedBell, bell_coe, NormalizedVector.ket_apply, invSqrt2_enorm_sq]

/-- The first Bell wire has a fair one outcome. -/
lemma first_one_probability :
    firstZ.outcomePMF placedBell ![true] = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply, firstOneFiber]
  simp [placedBell, bell_coe, NormalizedVector.ket_apply, invSqrt2_enorm_sq]

/-- The full Bell readout gives `00` with probability one half. -/
lemma both_zero_probability :
    bothZ.outcomePMF placedBell ![false, false] = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply, bothZeroFiber]
  simp [placedBell, bell_coe, NormalizedVector.ket_apply, invSqrt2_enorm_sq]

/-- The full Bell readout gives `11` with probability one half. -/
lemma both_one_probability :
    bothZ.outcomePMF placedBell ![true, true] = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply, bothOneFiber]
  simp [placedBell, bell_coe, NormalizedVector.ket_apply, invSqrt2_enorm_sq]

/-- A mismatched Bell result is impossible even though each marginal is fair. -/
lemma both_mismatch_probability :
    bothZ.outcomePMF placedBell ![false, true] = 0 := by
  rw [TerminalZMeasure.outcomePMF_apply, bothMismatchFiber]
  simp [placedBell, bell_coe, NormalizedVector.ket_apply]

/-- Measuring the first physical wire keeps every external reference coordinate. -/
def firstWireReadout {Reference : Register}
    (basis : (Register.prod (Qubits 2) Reference).Index) : Bool :=
  basis.1.val.testBit 1

/-- Two actual Z updates of the same wire cannot record different results,
for any initial joint state with an arbitrary external reference. -/
lemma repeated_first_wire_flip_zero {Reference : Register}
    (ρ : DensityOperator (Register.prod (Qubits 2) Reference))
    (first second : Bool) (different : second ≠ first) :
    (((ExecutionState.ofValue () ρ).measureZ firstWireReadout).measureZ
      firstWireReadout).block (((), first), second) =
        DensityOperator.zero (Register.prod (Qubits 2) Reference) := by
  simp only [ExecutionState.measureZ_block, ExecutionState.ofValue_block]
  rw [ZMeasurement.repeat_branch]
  simp [different]

end

end QuantumAlg.BellStatePreparation.Measurement
