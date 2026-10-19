/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Measure.Distribution

/-!
# Terminal measurement probability examples

These examples instantiate the typed terminal-Z probability law on the three
standard one-qubit states, then lock the logical/physical order of a reordered
partial measurement on a three-qubit register.
-/

section

namespace QuantumAlg.TerminalMeasureProbability

noncomputable section

/-- One logical qubit placed on physical system zero. -/
def oneQubitLayout : QubitLayout 1 where
  physical_idx := fun _ => 0
  physical_idx_injective := fun left right _ => Subsingleton.elim left right

/-- Full one-qubit terminal Z measurement. -/
def oneQubitMeasure : TerminalZMeasure oneQubitLayout 1 :=
  zMeasure oneQubitLayout

/-- Placed `|0>` input. -/
def placedKet0 : QubitLayout.State oneQubitLayout where
  state := PureState.basis 0 oneQubitLayout.systemIdx
  system_idx_eq := rfl

/-- Placed `|1>` input. -/
def placedKet1 : QubitLayout.State oneQubitLayout where
  state := PureState.basis 1 oneQubitLayout.systemIdx
  system_idx_eq := rfl

/-- Placed `|+>` input. -/
def placedKetPlus : QubitLayout.State oneQubitLayout where
  state := PureState.ofNormalized NormalizedVector.ketPlus
    oneQubitLayout.systemIdx
  system_idx_eq := rfl

/-- Canonical bit-vector output for computational basis zero. -/
def zeroOutcome : TerminalZMeasure.Outcome 1 :=
  fun _ => false

/-- Canonical bit-vector output for computational basis one. -/
def oneOutcome : TerminalZMeasure.Outcome 1 :=
  fun _ => true

@[simp] lemma oneQubitMeasure_readout_zero :
    oneQubitMeasure.readout 0 = zeroOutcome := by
  funext outputIndex
  fin_cases outputIndex
  decide

@[simp] lemma oneQubitMeasure_readout_one :
    oneQubitMeasure.readout 1 = oneOutcome := by
  funext outputIndex
  fin_cases outputIndex
  decide

private lemma zeroOutcome_fiber :
    Finset.univ.filter
        (fun basis : Fin (2 ^ 1) =>
          oneQubitMeasure.readout basis = zeroOutcome) = {0} := by
  decide

private lemma oneOutcome_fiber :
    Finset.univ.filter
        (fun basis : Fin (2 ^ 1) =>
          oneQubitMeasure.readout basis = oneOutcome) = {1} := by
  decide

lemma measureKet0_zero_probability_one :
    oneQubitMeasure.outcomePMF placedKet0 zeroOutcome = 1 := by
  rw [TerminalZMeasure.outcomePMF_apply]
  rw [zeroOutcome_fiber]
  simp [placedKet0]

lemma measureKet1_one_probability_one :
    oneQubitMeasure.outcomePMF placedKet1 oneOutcome = 1 := by
  rw [TerminalZMeasure.outcomePMF_apply]
  rw [oneOutcome_fiber]
  simp [placedKet1]

lemma measureKetPlus_zero_probability_half :
    oneQubitMeasure.outcomePMF placedKetPlus zeroOutcome = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply]
  rw [zeroOutcome_fiber]
  simp [placedKetPlus, NormalizedVector.ketPlus_apply]

lemma measureKetPlus_one_probability_half :
    oneQubitMeasure.outcomePMF placedKetPlus oneOutcome = (2 : ENNReal)⁻¹ := by
  rw [TerminalZMeasure.outcomePMF_apply]
  rw [oneOutcome_fiber]
  simp [placedKetPlus, NormalizedVector.ketPlus_apply]

lemma oneQubitOutcomePMF_total (state : QubitLayout.State oneQubitLayout) :
    ∑' outcome, oneQubitMeasure.outcomePMF state outcome = 1 :=
  TerminalZMeasure.outcomePMF_total oneQubitMeasure state

/-- Three logical qubits placed on distinct, nonconsecutive physical systems. -/
def threeQubitLayout : QubitLayout 3 where
  physical_idx := ![3, 7, 11]
  physical_idx_injective := by decide

/-- Measure logical qubits two then zero, leaving logical qubit one unmeasured. -/
def partialReorderedMeasure : TerminalZMeasure threeQubitLayout 2 :=
  zMeasureAt threeQubitLayout ![2, 0] (by decide)

/-- Explicit output obtained from basis state `|100⟩` in the selected order. -/
def partialReorderedOutcome : TerminalZMeasure.Outcome 2 :=
  ![false, true]

/-- Placed computational-basis state `|100⟩`. -/
def placedKet4 : QubitLayout.State threeQubitLayout where
  state := PureState.basis 4 threeQubitLayout.systemIdx
  system_idx_eq := rfl

@[simp] lemma partialReordered_systemIdx :
    partialReorderedMeasure.systemIdx = [11, 3] := by
  decide

@[simp] lemma partialReordered_readout_four :
    partialReorderedMeasure.readout 4 = partialReorderedOutcome := by
  funext outputIndex
  fin_cases outputIndex <;> decide

private lemma partialReorderedOutcome_fiber :
    Finset.univ.filter
        (fun basis : Fin (2 ^ 3) =>
          partialReorderedMeasure.readout basis = partialReorderedOutcome) =
      {4, 6} := by
  decide

lemma partialKet4_probability_one :
    partialReorderedMeasure.outcomePMF placedKet4 partialReorderedOutcome = 1 := by
  rw [TerminalZMeasure.outcomePMF_apply]
  rw [partialReorderedOutcome_fiber]
  simp [placedKet4]

end

end QuantumAlg.TerminalMeasureProbability

end
