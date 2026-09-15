/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Batch.Values
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.TerminalDecode.Resources

/-!
# Native materialization of a short-log terminal index

The existing shift-and-increment decoder reads the actual stored terminal
bits in their measured order. Its materialized word is exactly the original
full-register index used by pair recovery. The high and low source integers
are therefore its quotient and remainder at the original register split.
Every initial accumulator is allowed, including the zero-width boundary.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- The pure value of one existing terminal cell in the original source convention. -/
def terminalValue (value : CShape.Value (.bits ((ell + m) + ell))) :
    BatchRecovery.ShortLogTerminalBits m ell :=
  match value with
  | .bits bits => bits

/-- Materialize the terminal's integer using the actual ordered shift/increment circuit. -/
def terminalCircuit (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) : Circuit ctx ctx :=
  TerminalDecode.into .bigEndian input output

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The exact store and recorded path of the decoder's actual bit fold. -/
def terminalStep (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) (store : Store ctx) :
    Store ctx × (terminalCircuit input output).Path :=
  TerminalDecode.foldStep output (List.ofFn (fun index => .bitsGet input index)) store

/-- Complete mixed-state execution is the actual store map on every external reference. -/
theorem nativeRecovery_terminal_execute (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (terminalCircuit input output).execute Reference state =
      state.mapClassical (fun entry =>
        ((terminalStep input output entry.1).1,
          (entry.2, (terminalStep input output entry.1).2))) :=
  TerminalDecode.terminalDecode_fold_execute output
    (List.ofFn (fun index => .bitsGet input index)) Reference state

/-- The actual overwritten word is the source index, without a clean-input premise. -/
theorem nativeRecovery_terminal_index (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) (store : Store ctx)
    (separate : output.key ∉ input.storageKeys) :
    ((terminalStep input output store).1.read (TerminalDecode.writeInput output)).toNat =
      (BatchRecovery.decodeFullRegisterIndex m ell (terminalValue (store.read input))).val := by
  have decoded := TerminalDecode.terminalDecode_intoFromBitRefs_read_output .bigEndian
    (fun index => CInputRef.bitsGet input index) output store (fun _ => separate)
  refine decoded.trans ?_
  change (ClassicalAlgorithms.TerminalDecode.eval
    ⟨.bigEndian, fun index => ((store.read input).bitGet index).toBool⟩).val = _
  cases stored : store.read input with
  | bits bits =>
      exact ClassicalAlgorithms.TerminalDecode.eval_bigEndian_val bits

/-- The stored integer's high quotient is precisely the original first short-log sample. -/
theorem nativeRecovery_terminal_first (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) (store : Store ctx)
    (separate : output.key ∉ input.storageKeys) :
    ((terminalStep input output store).1.read (TerminalDecode.writeInput output)).toNat / 2 ^ ell =
      (BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read input))).1.val := by
  rw [nativeRecovery_terminal_index input output store separate]
  exact (BatchRecovery.decodeTerminalSample_fst_val m ell _).symm

/-- The stored integer's low remainder is precisely the original second short-log sample. -/
theorem nativeRecovery_terminal_second (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell))) (store : Store ctx)
    (separate : output.key ∉ input.storageKeys) :
    ((terminalStep input output store).1.read (TerminalDecode.writeInput output)).toNat % 2 ^ ell =
      (BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read input))).2.val := by
  rw [nativeRecovery_terminal_index input output store separate]
  exact (BatchRecovery.decodeTerminalSample_snd_val m ell _).symm

/-- Both actual native operation coordinates use the decoder's independent fixed-width allowance. -/
theorem nativeRecovery_terminal_pool_le (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell)))
    (path : (terminalCircuit input output).Path) :
    (terminalCircuit input output).resourcePool path ≤
      TerminalDecode.envelope ((ell + m) + ell) :=
  TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .bigEndian
    (fun index => .bitsGet input index) output path

/-- Actual serial depth charges each possible shift and selected increment. -/
theorem nativeRecovery_terminal_depth_le (input : CInputRef ctx (.bits ((ell + m) + ell)))
    (output : CWriteRef ctx (.unsignedWord ((ell + m) + ell)))
    (path : (terminalCircuit input output).Path) :
    (terminalCircuit input output).depth (fun _ => 1) path ≤ 2 * ((ell + m) + ell) := by
  have bound := TerminalDecode.terminalDecode_intoFromBitRefs_depth_le .bigEndian
    (fun index => CInputRef.bitsGet input index) output (fun _ => 1) path
  change (TerminalDecode.intoFromBitRefs .bigEndian
    (fun index => CInputRef.bitsGet input index) output).depth (fun _ => 1) path ≤ _
  exact bound.trans (Nat.le_of_eq (by omega))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery
