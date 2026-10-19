/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Redraw
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Persistent EH sample slots across a real source redraw

Redraw overwrites only the original source and parameter cells. Each earlier
sample slot remains a distinct retained cell with its full prior value.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma sampleRef_ne_liftSamples {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (width : Nat) (ref : CWriteRef ctx shape) (count : Nat)
    (index : Fin count) :
    (Native.Batch.Slots.sampleRef ctx width count index).key ≠
      (Native.Batch.Slots.liftSamples width ref count).key := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ih previous) index
      intro same
      change (Native.Batch.Slots.samples ctx width count).canonicalFreshKey =
        (Native.Batch.Slots.liftSamples width ref count).key at same
      apply (Native.Batch.Slots.samples ctx width count).canonicalFreshKey_fresh
      have present := MeasurementCells.reference_key_mem
        (Native.Batch.Slots.liftSamples width ref count).toCStorageRef
      exact same.symm ▸ present

attribute [local irreducible] Native.Batch.Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- No terminal slot shares the complete parameter's retained key. -/
lemma terminal_parameter_ne (index : Fin 16) :
    (terminalRef base noQuantum N index).key ≠
      (parameterRef base noQuantum N).key := by
  intro same
  have leftKey := underBank_key base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N index)
  have rightKey := underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))
  exact sampleRef_ne_liftSamples (measurementBits N)
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N) 16 index
    ((leftKey.symm.trans same).trans rightKey)

/-- No terminal slot shares the random residue source's retained key. -/
lemma terminal_source_ne (index : Fin 16) :
    (terminalRef base noQuantum N index).key ≠
      (sourceRef base noQuantum N).key := by
  intro same
  have leftKey := underBank_key base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N index)
  have rightKey := underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact sampleRef_ne_liftSamples (measurementBits N)
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N) 16 index
    ((leftKey.symm.trans same).trans rightKey)

/-- Structural reads separated from the two actual redraw destinations. -/
structure RedrawSeparated {shape : CShape}
    (observed : CInputRef (context base noQuantum N) shape) : Prop where
  source : (sourceRef base noQuantum N).key ∉ observed.storageKeys
  parameter : (parameterRef base noQuantum N).key ∉ observed.storageKeys

/-- Every terminal slot is separated from both actual redraw writes. -/
lemma terminal_redraw_separated (index : Fin 16) :
    RedrawSeparated base noQuantum N
      (.storage (terminalRef base noQuantum N index).toCStorageRef) := by
  constructor
  · intro member
    exact (terminal_source_ne base noQuantum N index).symm
      (List.mem_singleton.mp member)
  · intro member
    exact (terminal_parameter_ne base noQuantum N index).symm
      (List.mem_singleton.mp member)

include input in
/-- A real random redraw leaves any separated old structural value intact. -/
lemma redraw_frame_read {shape : CShape}
    (observed : CInputRef (context base noQuantum N) shape)
    (separated : RedrawSeparated base noQuantum N observed)
    (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (redrawStep base noQuantum N store value).1.read observed =
      store.read observed := by
  have actual := congrArg (fun next : Store (context base noQuantum N) =>
    next.read observed) (redraw_store base noQuantum N input store value)
  exact actual.trans ((Store.read_write_of_not_mem_storageKeys _ _ _ observed
    separated.parameter).trans
      (Store.read_write_of_not_mem_storageKeys _ _ _ observed separated.source))

include input in
/-- Every earlier sample survives the actual next-batch redraw. -/
lemma redraw_terminal (index : Fin 16)
    (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (redrawStep base noQuantum N store value).1.read
      (.storage (terminalRef base noQuantum N index).toCStorageRef) =
    store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) :=
  redraw_frame_read base noQuantum N input _
    (terminal_redraw_separated base noQuantum N index) store value

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
