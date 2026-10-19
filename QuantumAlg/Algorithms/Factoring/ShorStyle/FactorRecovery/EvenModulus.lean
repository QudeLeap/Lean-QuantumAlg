/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Encoding
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# The original even-modulus exception executes and writes factor two

The actual flag is first cleared and then complemented, so its initial value
is unrestricted. The existing compiled constant-word program loads two into
the real payload cell before the actual option pack writes the result.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual two flag writes set true regardless of the original stored Boolean. -/
lemma even_flag (cells : Cells ctx N) (store : Store ctx) :
    ((store.applyOp (clearActiveOp cells)).applyOp (setActiveOp cells)).read (activeRead cells) =
      .bit true := by
  have cleared : (store.applyOp (clearActiveOp cells)).read (activeRead cells) = .bit false := by
    refine (Store.read_applyOp_output store (clearActiveOp cells)).trans ?_
    change Resource.BitOpcode.eval .xor
      (.product (store.read (activeRead cells)) (store.read (activeRead cells))) = .bit false
    cases store.read (activeRead cells) with
    | bit value => cases value <;> rfl
  refine (Store.read_applyOp_output (store.applyOp (clearActiveOp cells))
    (setActiveOp cells)).trans ?_
  change Resource.BitOpcode.eval .not
    ((store.applyOp (clearActiveOp cells)).read (activeRead cells)) = .bit true
  rw [cleared]
  rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The exact compiled payload-load record of the original even-modulus branch. -/
def twoStep (cells : Cells ctx N) (store : Store ctx) :
    Store ctx × (ConstantWord.circuit (model := model) cells.halfPower 2).Path :=
  ConstantWord.foldStep (model := model) cells.halfPower
    (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) store

/-- The real payload load followed by the real nominal result write. -/
def twoPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (ConstantWord.circuit (model := model) cells.halfPower 2)
      (BitWord.instruction (execution := model) (packOutputOp cells output))).Path :=
  let loaded := twoStep (model := model) cells store
  let packed := BitWord.instructionStep (execution := model) (packOutputOp cells output) loaded.1
  (packed.1, (loaded.2, packed.2))

/-- The true flag-setting operation precedes the real load and packaging record. -/
def setTwoPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (BitWord.instruction (execution := model) (setActiveOp cells))
      (.seq (ConstantWord.circuit (model := model) cells.halfPower 2)
        (BitWord.instruction (execution := model) (packOutputOp cells output)))).Path :=
  let set := BitWord.instructionStep (execution := model) (setActiveOp cells) store
  let selected := twoPackStep (model := model) cells output set.1
  (selected.1, (set.2, selected.2))

/-- The complete original even-modulus exception records every actually executed instruction. -/
def evenStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (evenModulus (model := model) cells output).Path :=
  let cleared := BitWord.instructionStep (execution := model) (clearActiveOp cells) store
  let selected := setTwoPackStep (model := model) cells output cleared.1
  (selected.1, (cleared.2, selected.2))

/-- The real exceptional branch writes exactly the source factor two, without truncation. -/
lemma even_result (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (larger : 2 < N) (separate : cells.halfPower.key ≠ cells.active.key) :
    (evenStep (model := model) cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (some 2) := by
  let selected := (store.applyOp (clearActiveOp cells)).applyOp (setActiveOp cells)
  let loaded := twoStep (model := model) cells selected
  have tag : loaded.1.read (activeRead cells) = .bit true :=
    (ConstantWord.constantWord_fold_read_other (model := model) cells.halfPower
      (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) (activeRead cells)
      (fun member => separate (List.mem_singleton.mp member)) selected).trans
        (even_flag cells store)
  have payload : (loaded.1.read (halfRead cells)).toNat = 2 :=
    (ConstantWord.constantWord_read (model := model) cells.halfPower 2 selected).trans
      (Nat.mod_eq_of_lt (larger.trans_le source.register_fits))
  refine (packOutput_result cells output loaded.1).trans ?_
  rw [tag, payload]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
