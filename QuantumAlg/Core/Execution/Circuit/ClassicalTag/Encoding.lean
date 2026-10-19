/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag

/-!
# Exact execution with a classical spectator encoded in the external reference

Orthogonal reference blocks represent the complete classical spectator while
retaining every original store, service, history and reference correlation.
The actual fixed-context execution followed by diagonal decoding recovers the
execution with that spectator in history. This is a mathematical reference
extension, not an instruction that allocates a physical tag register.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution.State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {Hidden H : Type} [Fintype Hidden] [Fintype H]

/-- Encode only the spectator beside the original reference and retain service and history. -/
def encodeOracleTag (state : State ctx Reference (Hidden × (H × Tag.Index))) :
    State ctx (Tag.prod Reference) (Hidden × H) :=
  encodeReferenceTag (state.mapHistory (Equiv.prodAssoc Hidden H Tag.Index).symm)

/-- Encoding the complete spectator distribution preserves its total mass exactly. -/
lemma encodeOracleTag_mass (state : State ctx Reference (Hidden × (H × Tag.Index))) :
    (encodeOracleTag state).mass = state.mass :=
  (encodeReferenceTag_mass _).trans (mapHistory_mass state _)

/-- Decoding recovers every complete original block, not only its probability or marginal. -/
lemma decode_encodeOracleTag (state : State ctx Reference (Hidden × (H × Tag.Index))) :
    decodeOracleTag (encodeOracleTag state) = state := by
  rw [encodeOracleTag, decodeOracleTag, decode_encodeReferenceTag]
  rw [mapHistory_comp]
  dsimp only [mapHistory]
  calc
    _ = state.mapClassical id := ExecutionState.executionState_mapClassical_congr state rfl
    _ = state := ExecutionState.mapClassical_id state

/-- Each encoded reference tag contains exactly its original joint history block. -/
lemma encodeOracleTag_entry (state : State ctx Reference (Hidden × (H × Tag.Index)))
    (store : Store ctx) (hidden : Hidden) (history : H) (leftTag rightTag : Tag.Index)
    (row column : (ctx.register.prod Reference).Index) :
    ((encodeOracleTag state).block (store, (hidden, history))).matrix
        (row.1, (leftTag, row.2)) (column.1, (rightTag, column.2)) =
      if leftTag = rightTag then
        (state.block (store, (hidden, (history, leftTag)))).matrix row column else 0 := by
  rw [encodeOracleTag, encodeReferenceTag_entry, mapHistory_equiv_entry]
  rfl

end Execution.State

namespace Circuit

/-- Executing with an encoded spectator and decoding yields the same complete actual result. -/
lemma execute_encodedClassicalTag
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (environment : model.Environment)
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × (H × Tag.Index))) :
    code.execute environment Reference state =
      State.decodeExecutionTag
        (code.execute environment (Tag.prod Reference) (State.encodeOracleTag state)) := by
  simpa only [State.decode_encodeOracleTag] using
    code.execute_decodeReferenceTag environment (State.encodeOracleTag state)

end Circuit

end

end QuantumAlg
