/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Correctness
import all QuantumAlg.Components.Classical.GF2.Native.State.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Original recovery through the actual seven-cell allocation

The real allocation establishes every initialized-cell and separation fact.
The returned caller store is exactly one write of the original recovery of
its actual input rows. The same record proves the full interpreter equation,
including arbitrary quantum-reference blocks and classical histories.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution ClassicalWorkspace

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- Original big-endian row decoding and optional polynomial recovery encoding. -/
def gf2RecoveryValue (values : CShape.Value (.fixedVector rowCount (.bits width))) :
    CShape.Value (.option (.unsignedWord width)) :=
  match ClassicalAlgorithms.GF2.recover? (fun row =>
    ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian (values.get row))) with
  | none => .optionNone
  | some word => .optionSome (.unsignedWord word)

/-- Actual initialized allocation returns one exact recovery write and the same full record. -/
theorem gf2WithState_actualRecord_correct
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ∃ record : Store ctx → Store ctx × (withState input output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withState input output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (record before).1 = before.write output (gf2RecoveryValue (before.read input)) := by
  apply withCells_actualRecord_initialized_post ctx (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    (fun before after => after = before.write output (gf2RecoveryValue (before.read input)))
  intro inner cells distinct transport separated
  let step := intoStep (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output)
  refine ⟨step, ?_, ?_⟩
  · exact gf2Into_execute (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
      (transport.liftWrite output)
  · intro source before reads initialized
    let after := (step before).1
    let target := transport.restrict after
    have projected : transport.ReadsAs target after :=
      transport.workspaceTransport_restrict_readsAs after
    refine ⟨target, ?_, projected⟩
    apply Store.store_eq_write_of_read_frame source target output
      (gf2RecoveryValue (source.read input))
    · have written : after.read (.storage (transport.liftWrite output).toCStorageRef) =
          gf2RecoveryValue (source.read input) := by
        apply gf2Into_cellOutput input output cells distinct transport separated before initialized
          (fun row => ClassicalAlgorithms.TerminalDecode.eval
            (TerminalDecode.decodeInput .bigEndian ((source.read input).get row)))
        intro row
        rw [reads input]
      calc
        target.read (.storage output.toCStorageRef) =
            after.read (transport.liftInput (.storage output.toCStorageRef)) :=
          (projected (.storage output.toCStorageRef)).symm
        _ = gf2RecoveryValue (source.read input) := by
          rw [Transport.liftWrite_input]
          exact written
    · intro shape other different
      have free : output.key ∉ (CInputRef.storage other).storageKeys := by
        simpa only [CInputRef.storageKeys, List.mem_singleton] using different
      exact (projected (.storage other)).symm.trans
        ((gf2Into_cellFrame input output cells transport separated before
          (.storage other) free).trans (reads (.storage other)))

end

end QuantumAlg.ClassicalRoutines.GF2.Native
