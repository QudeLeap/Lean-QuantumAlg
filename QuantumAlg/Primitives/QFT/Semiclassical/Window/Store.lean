/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Instrument
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Outputs

/-!
# Real retained outcomes and causal earlier-window reads

The corrected program performs exactly the same ordered native MZ writes as
the original generic output-prefix construction. Distinct original keys retain
all actual measured values. Writes in the current window preserve every cell
from an earlier chronological position, regardless of its initial value.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

lemma measuredOutput_tail (ports : Ports ctx totalBits (active + 1)) (index : Fin active) :
    ports.tail.measuredOutput index = ports.measuredOutput index.succ := by
  unfold Ports.measuredOutput
  rw [Ports.tail_output]
  rfl

/-- The recursive actual MZ writes are the existing generic ordered write prefix. -/
lemma window_outcomeStore_eq_prefix (count : Nat) (ports : Ports ctx totalBits count)
    (original : Store ctx) (outcome : Bits count) :
    outcomeStore count ports original outcome =
      _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.outcomeStore
        ports.wires ports.qubits ports.measuredOutput original outcome := by
  induction count generalizing original with
  | zero => rfl
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      rw [outcomeStore, ih,
        _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.outcomeStore_head_tail]
      exact congrArg
        (fun outputs : ∀ index,
          CWriteRef ctx (.finite (ctx.quantumLayout.wire (ports.tail.wires index)).dimension) =>
          _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.outcomeStore
            ports.tail.wires ports.tail.qubits outputs
            (original.write (ports.measuredOutput 0) (.finite (headOutcome ports head))) tail)
        (funext (measuredOutput_tail ports))

/-- Every actual dimension-cast measured cell retains its own source outcome after all writes. -/
lemma window_outcomeStore_measured_read (ports : Ports ctx totalBits active)
    (original : Store ctx) (outcome : Bits active) (index : Fin active) :
    (outcomeStore active ports original outcome).read
        (.storage (ports.measuredOutput index).toCStorageRef) =
      outcomeValues ports.wires ports.qubits outcome index := by
  rw [window_outcomeStore_eq_prefix]
  exact _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.outcomeStore_read
    ports.wires ports.qubits ports.measuredOutput
    (fun left right same => ports.output_keys_injective
      ((ports.measuredOutput_key left).symm.trans
        (same.trans (ports.measuredOutput_key right)))) original outcome index

/-- The original binary cell reads the same actual bit, without a packing instruction. -/
lemma window_outcomeStore_binary_read (ports : Ports ctx totalBits active)
    (original : Store ctx) (outcome : Bits active) (index : Fin active) :
    ((outcomeStore active ports original outcome).read
        (.storage (ports.output index).toCStorageRef)).toFin.val =
      (tupleCoordinates active outcome index).val := by
  have measured := congrArg
    (fun value : CShape.Value (.finite (ctx.quantumLayout.wire (ports.wires index)).dimension) =>
      value.toFin.val)
    (window_outcomeStore_measured_read ports original outcome index)
  change (((outcomeStore active ports original outcome).read
    (.storage (QubitReadouts.outputAt _ (ports.qubits index)
      (ports.output index)).toCStorageRef)).toFin.val) = _ at measured
  rw [QubitReadouts.outputAt_read] at measured
  exact measured

/-- Every differently named original cell survives the actual window writes. -/
lemma window_outcomeStore_read_untouched (count : Nat) (ports : Ports ctx totalBits count)
    (original : Store ctx) (outcome : Bits count) {shape : CShape}
    (ref : CStorageRef ctx shape) (separate : ∀ index, (ports.output index).key ≠ ref.key) :
    (outcomeStore count ports original outcome).read (.storage ref) =
      original.read (.storage ref) := by
  induction count generalizing original with
  | zero => rfl
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      have tailSeparate : ∀ index, (ports.tail.output index).key ≠ ref.key := by
        intro index
        rw [Ports.tail_output]
        exact separate index.succ
      refine (ih ports.tail
        (original.write (ports.measuredOutput 0) (.finite (headOutcome ports head))) tail
        tailSeparate).trans ?_
      exact Store.read_write_other original (ports.measuredOutput 0) ref _
        (fun same => separate 0 ((ports.measuredOutput_key 0).symm.trans same))

/-- Later window execution retains each earlier same-stream outcome used by real feedback. -/
lemma window_outcomeStore_past_read (ports : Ports ctx totalBits active)
    (original : Store ctx) (outcome : Bits active) (previous : BitPosition totalBits)
    (past : ports.past previous) :
    (outcomeStore active ports original outcome).read
        (.storage (ports.results previous).toCStorageRef) =
      original.read (.storage (ports.results previous).toCStorageRef) := by
  apply window_outcomeStore_read_untouched
  intro index same
  have equal := ports.results_injective same
  have positions := congrArg (fun position : BitPosition totalBits => position.2.val) equal
  change ports.start + index.val = previous.2.val at positions
  have prior := past.2
  omega

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
