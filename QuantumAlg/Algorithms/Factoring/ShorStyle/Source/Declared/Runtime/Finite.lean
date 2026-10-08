/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing

/-!
# Actual arbitrary-count declared Shor recovery on one physical bank

Each chronological round includes actual sampling, native recovery, persistent
first-success selection and the original bank's physical zero reset. Earlier
source results remain in their real retained cells. The final optional result
is packed exactly once after the finite loop. The entire original caller enters
through actual persistent allocation, clearing and one quantum preparation.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The exact final live context after the requested chronological number of retained rounds. -/
def context (ctx : RuntimeCtx .quantum) (N : Nat) : Nat → RuntimeCtx .quantum
  | 0 => ctx
  | count + 1 => context (Iteration.context ctx N) N count

/-- Every original writable entry keeps its key beneath all actual later source allocations. -/
def liftWrite {shape : CShape} (ctx : RuntimeCtx .quantum) (N : Nat) (count : Nat)
    (original : CWriteRef ctx shape) : CWriteRef (context ctx N count) shape :=
  match count with
  | 0 => original
  | count + 1 => liftWrite (Iteration.context ctx N) N count (Completion.liftWrite ctx N original)

/-- The same four actual selector cells remain live throughout the finite loop. -/
def cells (ctx : RuntimeCtx .quantum) (N count : Nat) (original : NativeFactorScan.Cells ctx N) :
    NativeFactorScan.Cells (context ctx N count) N where
  candidate := liftWrite ctx N count original.candidate
  accepted := liftWrite ctx N count original.accepted
  selected := liftWrite ctx N count original.selected
  scratch := liftWrite ctx N count original.scratch

/-- Every finite retained round preserves the bank's exact ordered physical wire list. -/
theorem quantumWires (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).quantumWires = ctx.quantumWires := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact (induction (Iteration.context ctx N)).trans (Iteration.quantumWires ctx N)

/-- Repeat the real complete chronological body, with actual lifted persistent destinations. -/
def body (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (count : Nat) → Circuit (executionModel input) ctx (context ctx N count)
  | 0 => Circuit.id (model := executionModel input) ctx
  | count + 1 => (Completion.code ctx N input sameWires original result).seq
      (body (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)
        (Completion.cells ctx N original) (Completion.liftWrite ctx N result) count)

/-- The sole terminal optional encoding is one real paid pack of the actual latches. -/
def pack (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N) (count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (executionModel input) (context ctx N count) (context ctx N count) :=
  BitWord.instruction (execution := executionModel input)
    (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result))

/-- The complete finite tail runs all real rounds before the one terminal pack. -/
def code (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Circuit (executionModel input) ctx (context ctx N count) :=
  (body ctx N input sameWires original result count).seq (pack ctx N input count original result)

/-- Every arbitrary-count actual tail keeps the physical seed established
by the real initializer. -/
theorem body_seeded (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (context ctx N count).quantumLayout.zeroLabel
      ((body ctx N input sameWires original result count).execute Reference state) := by
  induction count generalizing ctx History with
  | zero =>
      change BasisSeeded.Holds ctx.quantumLayout.zeroLabel
        ((Circuit.id (model := executionModel input) ctx).execute Reference state)
      rw [Circuit.execute_id]
      exact BasisSeeded.mapStore _ state seeded id
        (fun entry => (entry.2.1, (entry.2.2, ())))
  | succ count induction =>
      exact BasisSeeded.seq (Completion.code ctx N input sameWires original result)
        (body (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N original) (Completion.liftWrite ctx N result) count) _ state
        (induction (Iteration.context ctx N) ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N original) (Completion.liftWrite ctx N result)
          ((Completion.code ctx N input sameWires original result).execute Reference state)
          (Completion.code_seeded ctx N input sameWires original result state))

/-- Final real classical packing preserves every complete zero-bank/reference block. -/
theorem pack_seeded (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N) (count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context ctx N count) Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds (context ctx N count).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (context ctx N count).quantumLayout.zeroLabel
      ((pack ctx N input count original result).execute Reference state) := by
  rw [pack, BitWord.bitWord_instruction_execute]
  exact BasisSeeded.mapStore _ state seeded
    (fun store => (BitWord.instructionStep (execution := executionModel input)
      (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result))
        store).1)
    (fun entry => (entry.2.1, (entry.2.2,
      (BitWord.instructionStep (execution := executionModel input)
        (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result))
          entry.1).2)))

/-- The finite complete tail and its final paid pack keep the same physical seed. -/
theorem code_seeded (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (context ctx N count).quantumLayout.zeroLabel
      ((code ctx N input sameWires count original result).execute Reference state) :=
  BasisSeeded.seq (body ctx N input sameWires original result count)
    (pack ctx N input count original result) _ state
    (pack_seeded ctx N input count original result _
      (body_seeded ctx N input sameWires count original result state seeded))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
