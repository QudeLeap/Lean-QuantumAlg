/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Util.Nat.FixedWidth.Window.Chronology

/-!
# Existing wires and retained result cells for one recycled Fourier window

Chronological positions run from the high source bit to the low source bit.
Only the active injection is selected; every other system remains in the
ambient context. The same two-stream cell family survives every window.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

abbrev BitPosition (totalBits : Nat) := Fin 2 × Fin totalBits

/-- A window selects existing physical qubits and original writable result cells. -/
structure Ports (ctx : RuntimeCtx .quantum) (totalBits active : Nat) where
  stream : Fin 2
  start : Nat
  within : start + active ≤ totalBits
  wires : Fin active ↪ Fin ctx.systemCount
  qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2
  results : BitPosition totalBits → CWriteRef ctx (.finite 2)
  results_injective : Function.Injective (fun index => (results index).key)

namespace Ports

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

def position (ports : Ports ctx totalBits active) (index : Fin active) : Fin totalBits :=
  ⟨ports.start + index.val,
    (Nat.add_lt_add_left index.isLt ports.start).trans_le ports.within⟩

/-- The actual source bit has the original little-endian coordinate. -/
def sourceBit (ports : Ports ctx totalBits active) (index : Fin active) : Fin totalBits :=
  Fin.rev (ports.position index)

lemma sourceBit_val (ports : Ports ctx totalBits active) (index : Fin active) :
    (ports.sourceBit index).val = totalBits - (ports.start + index.val + 1) := rfl

def output (ports : Ports ctx totalBits active) (index : Fin active) :
    CWriteRef ctx (.finite 2) := ports.results (ports.stream, ports.position index)

def measuredOutput (ports : Ports ctx totalBits active) (index : Fin active) :
    CWriteRef ctx (.finite (ctx.quantumLayout.wire (ports.wires index)).dimension) :=
  QubitReadouts.outputAt _ (ports.qubits index) (ports.output index)

lemma measuredOutput_key (ports : Ports ctx totalBits active) (index : Fin active) :
    (ports.measuredOutput index).key = (ports.output index).key :=
  QubitReadouts.outputAt_key _ (ports.qubits index) (ports.output index)

lemma output_keys_injective (ports : Ports ctx totalBits active) :
    Function.Injective (fun index => (ports.output index).key) := by
  intro first second same
  have original := ports.results_injective same
  have values := congrArg (fun index : BitPosition totalBits => index.2.val) original
  apply Fin.ext
  change ports.start + first.val = ports.start + second.val at values
  omega

/-- Earlier windows in the same stream are the only possible external feedback sources. -/
def past (ports : Ports ctx totalBits active) (previous : BitPosition totalBits) : Prop :=
  previous.1 = ports.stream ∧ previous.2.val < ports.start

lemma past_before_position (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (index : Fin active) (prior : ports.past previous) :
    previous.2.val < (ports.position index).val := by
  change previous.2.val < ports.start + index.val
  exact prior.2.trans_le (Nat.le_add_right _ _)

/-- Recursive measurement drops one selected wire and retains all original result cells. -/
def tail (ports : Ports ctx totalBits (active + 1)) : Ports ctx totalBits active where
  stream := ports.stream
  start := ports.start + 1
  within := by have bounded := ports.within; omega
  wires := ⟨fun index => ports.wires index.succ,
    fun _ _ same => Fin.succ_injective active (ports.wires.injective same)⟩
  qubits := fun index => ports.qubits index.succ
  results := ports.results
  results_injective := ports.results_injective

lemma tail_position (ports : Ports ctx totalBits (active + 1)) (index : Fin active) :
    ports.tail.position index = ports.position index.succ := by
  apply Fin.ext
  change ports.start + 1 + index.val = ports.start + (index.val + 1)
  omega

lemma tail_output (ports : Ports ctx totalBits (active + 1)) (index : Fin active) :
    ports.tail.output index = ports.output index.succ := by
  change ports.results (ports.stream, ports.tail.position index) = _
  rw [tail_position]
  rfl

end Ports

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
