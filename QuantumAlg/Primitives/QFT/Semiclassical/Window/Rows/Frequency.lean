/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Feedback

/-!
# Explicit frequency labels of the same physical window rows

Physical outcomes remain in chronological measurement order. The first
physical outcome is the least significant local Fourier-frequency bit, as
in the original no-SWAP source bridge. These mathematical row equalities
do not change writable cells, move quantum systems or implement classical
packing. A later window's earlier-result phase word remains present.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

/-- The existing source bridge interprets physical outcomes as low-frequency bits first. -/
def decodedWindowFrequency (count : Nat) (outcome : Bits count) : Fin (2 ^ count) :=
  qftReverseBits count (binaryEquiv count outcome)

/-- Selecting a frequency's physical outcome tuple returns that same frequency label. -/
lemma decodedWindowFrequency_frequencyBits (count : Nat) (frequency : Fin (2 ^ count)) :
    decodedWindowFrequency count (frequencyBits count frequency) = frequency := by
  rw [decodedWindowFrequency, qftSemiclassical_frequencyBits_physicalLabel,
    qftReverseBits_involutive]

/-- This is a bijection of mathematical labels; the physical bank and result cells stay fixed. -/
lemma frequencyBits_decodedWindowFrequency (count : Nat) (outcome : Bits count) :
    frequencyBits count (decodedWindowFrequency count outcome) = outcome := by
  unfold frequencyBits decodedWindowFrequency
  rw [qftReverseBits_involutive, Equiv.symm_apply_apply]

/-- The frozen signed source row has the explicit negative Fourier-frequency coefficient. -/
lemma window_signedSource_frequency_entry (count : Nat) (outcome input : Bits count) :
    signedSourceMatrix true count outcome input =
      star (QFTOperator count (decodedWindowFrequency count outcome)
        (binaryEquiv count input)) := by
  rw [signedSourceMatrix_inverse OracleModel.empty count OracleModel.emptyInterpretation]
  change star (sourceMatrix OracleModel.empty count OracleModel.emptyInterpretation
    outcome input) = _
  rw [← qftSemiclassical_coherent_eq_sourceMatrix OracleModel.empty
    OracleModel.emptyInterpretation, qftSemiclassical_coherent_entry]
  rfl

/-- The true source window keeps its physical zero bank, full remainder and real prior feedback. -/
lemma window_source_frequency_entry (ports : Ports ctx totalBits active) (Reference : Register)
    (original : Store ctx) (outcome : Bits active)
    (row column : (ctx.register.prod Reference).Index) :
    sourceWindowKraus ports Reference original outcome row column =
      if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
            Partner.zeroBits active ∧
          (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
            (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
        star (QFTOperator active (decodedWindowFrequency active outcome)
            (binaryEquiv active
              (referenceBankCoordinates ports.wires ports.qubits Reference column).1)) *
          Feedback.wordScalar ports original column.1 (List.finRange active)
      else 0 := by
  unfold sourceWindowKraus
  rw [window_signedSource_frequency_entry]

/-- The same executed native feedback/readout word has that explicitly decoded frequency row. -/
lemma window_native_frequency_entry (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (original : Store ctx) (outcome : Bits active)
    (row column : (ctx.register.prod Reference).Index) :
    (outcomeKraus environment Reference active ports outcome *
      Feedback.wordOperator ports environment Reference original (List.finRange active))
        row column =
      if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
            Partner.zeroBits active ∧
          (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
            (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
        star (QFTOperator active (decodedWindowFrequency active outcome)
            (binaryEquiv active
              (referenceBankCoordinates ports.wires ports.qubits Reference column).1)) *
          Feedback.wordScalar ports original column.1 (List.finRange active)
      else 0 :=
  (window_feedbackKraus_source_entry ports environment Reference original outcome row column).trans
    (window_source_frequency_entry ports Reference original outcome row column)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
