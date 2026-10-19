/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Store

/-!
# Actual paid packing of recycled-control outcomes

One existing native packing
instruction reads the retained binary cells in each exponent's frequency
order and writes a caller-provided physical result cell. It allocates no
storage and changes no quantum matrix entry. This is the actual charged
classical instruction, rather than a mathematical output interpretation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Packing

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual native adapter reads existing cells and writes one existing packed destination. -/
def operation (result : CWriteRef (Context base noQuantum m ell width)
    (.bits (resultBits m ell))) :
    ClassicalOp (.fixedVector (resultBits m ell) (.finite 2)) (.bits (resultBits m ell))
      (Context base noQuantum m ell width) (Context base noQuantum m ell width) :=
  .packFiniteBits (resultBits m ell) (Context base noQuantum m ell width)
    (frequencyInput base noQuantum m ell width) result

/-- Exactly one selected native classical leaf materializes the reordered bit vector. -/
def code (result : CWriteRef (Context base noQuantum m ell width)
    (.bits (resultBits m ell))) :
    Circuit model (Context base noQuantum m ell width) (Context base noQuantum m ell width) :=
  BitWord.instruction (operation base noQuantum m ell width result)

variable (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))

/-- The instruction preserves the complete quantum state and every prior-history correlation. -/
lemma recyclingPacking_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    (code base noQuantum m ell width result).execute environment Reference state =
      state.mapClassical (fun entry =>
        let next := BitWord.instructionStep (execution := model)
          (operation base noQuantum m ell width result) entry.1
        (next.1, (entry.2.1, (entry.2.2, next.2)))) :=
  BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
    (operation base noQuantum m ell width result) state

/-- The destination contains the actual instruction's packed value from the pre-step store. -/
lemma recyclingPacking_output (store : Store (Context base noQuantum m ell width)) :
    (store.applyOp (operation base noQuantum m ell width result)).read
        (.storage result.toCStorageRef) =
      CShape.packFiniteBits (resultBits m ell)
        (store.read (frequencyInput base noQuantum m ell width)) :=
  Store.read_applyOp_output store (operation base noQuantum m ell width result)

/-- Every written Boolean bit recovers precisely its selected real binary input cell value. -/
lemma recyclingPacking_recovers (store : Store (Context base noQuantum m ell width))
    (index : Fin (resultBits m ell)) :
    (((operation base noQuantum m ell width result).eval
      (store.read (frequencyInput base noQuantum m ell width))).bitGet index).toBool.toNat =
        ((store.read (frequencyInput base noQuantum m ell width)).get index).toFin.val :=
  ClassicalOp.eval_packFiniteBits_recovers (resultBits m ell)
    (Context base noQuantum m ell width) (frequencyInput base noQuantum m ell width)
    result (store.read (frequencyInput base noQuantum m ell width)) index

/-- The first frequency word reverses only the first exponent's chronological output cells. -/
lemma recyclingPacking_first_frequency (store : Store (Context base noQuantum m ell width))
    (position : Fin (ell + m)) :
    (((operation base noQuantum m ell width result).eval
      (store.read (frequencyInput base noQuantum m ell width))).bitGet
        (Fin.castAdd ell position)).toBool.toNat =
      (store.read (.storage
        (firstCell base noQuantum m ell width position.rev).toCStorageRef)).toFin.val := by
  refine (recyclingPacking_recovers base noQuantum m ell width result store
    (Fin.castAdd ell position)).trans ?_
  change (store.read (Fin.addCases
    (fun index => .storage (firstCell base noQuantum m ell width index.rev).toCStorageRef)
    (fun index => .storage (secondCell base noQuantum m ell width index.rev).toCStorageRef)
    (Fin.castAdd ell position))).toFin.val = _
  rw [Fin.addCases_left]

/-- The second frequency word reverses its own cells without exchanging the two exponents. -/
lemma recyclingPacking_second_frequency (store : Store (Context base noQuantum m ell width))
    (position : Fin ell) :
    (((operation base noQuantum m ell width result).eval
      (store.read (frequencyInput base noQuantum m ell width))).bitGet
        (Fin.natAdd (ell + m) position)).toBool.toNat =
      (store.read (.storage
        (secondCell base noQuantum m ell width position.rev).toCStorageRef)).toFin.val := by
  refine (recyclingPacking_recovers base noQuantum m ell width result store
    (Fin.natAdd (ell + m) position)).trans ?_
  change (store.read (Fin.addCases
    (fun index => .storage (firstCell base noQuantum m ell width index.rev).toCStorageRef)
    (fun index => .storage (secondCell base noQuantum m ell width index.rev).toCStorageRef)
    (Fin.natAdd (ell + m) position))).toFin.val = _
  rw [Fin.addCases_right]

/-- Packing preserves every differently named physical cell, including prior output records. -/
lemma recyclingPacking_preserves_cell {shape : CShape}
    (store : Store (Context base noQuantum m ell width))
    (observed : CStorageRef (Context base noQuantum m ell width) shape)
    (different : result.key ≠ observed.key) :
    (store.applyOp (operation base noQuantum m ell width result)).read (.storage observed) =
      store.read (.storage observed) :=
  Store.read_write_other store result observed _ different

/-- Classical packing retains every bank/reference matrix entry after summing its actual records. -/
lemma recyclingPacking_quantumMarginal {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    ((code base noQuantum m ell width result).execute environment Reference state).quantumMarginal =
      state.quantumMarginal := by
  rw [recyclingPacking_execute]
  exact ExecutionState.mapClassical_quantumMarginal _ _

/-- Paid packing emits one width-indexed native classical operation on every actual path. -/
lemma recyclingPacking_eventTrace
    (path : (code base noQuantum m ell width result).Path) :
    (code base noQuantum m ell width result).eventTrace path =
      [Resource.Event.classicalOperation (model := model)
        (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packFiniteBits (resultBits m ell))))] :=
  BitWord.bitWord_instruction_eventTrace (execution := model)
    (operation base noQuantum m ell width result) path

/-- Its classical native event remains charged while its quantum time is zero. -/
lemma recyclingPacking_quantumTime
    (path : (code base noQuantum m ell width result).Path) :
    (code base noQuantum m ell width result).quantumTime path = 0 := by
  exact BitWord.bitWord_instruction_depth (execution := model)
    (operation base noQuantum m ell width result) Resource.Event.quantumDuration path

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Packing
