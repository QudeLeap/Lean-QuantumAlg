/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
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

/-- The exact compiled payload-load record of the original even-modulus branch. -/
def twoStep (cells : Cells ctx N) (store : Store ctx) :
    Store ctx × (ConstantWord.circuit cells.halfPower 2).Path :=
  ConstantWord.foldStep cells.halfPower
    (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) store

/-- The real payload load followed by the real nominal result write. -/
def twoPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (ConstantWord.circuit cells.halfPower 2)
      (.classical (packOutputOp cells output))).Path :=
  let loaded := twoStep cells store
  (loaded.1.applyOp (packOutputOp cells output), (loaded.2, ()))

/-- The true flag-setting operation precedes the real load and packaging record. -/
def setTwoPackStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (.classical (setActiveOp cells))
      (.seq (ConstantWord.circuit cells.halfPower 2)
        (.classical (packOutputOp cells output)))).Path :=
  let selected := twoPackStep cells output (store.applyOp (setActiveOp cells))
  (selected.1, ((), selected.2))

/-- The complete original even-modulus exception records every actually executed instruction. -/
def evenStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (evenModulus cells output).Path :=
  let selected := setTwoPackStep cells output (store.applyOp (clearActiveOp cells))
  (selected.1, ((), selected.2))

/-- The actual two flag writes set true regardless of the original stored Boolean. -/
theorem even_flag (cells : Cells ctx N) (store : Store ctx) :
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

/-- The real exceptional branch writes exactly the source factor two, without truncation. -/
theorem even_result (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (larger : 2 < N) (separate : cells.halfPower.key ≠ cells.active.key) :
    (evenStep cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (some 2) := by
  let selected := (store.applyOp (clearActiveOp cells)).applyOp (setActiveOp cells)
  let loaded := twoStep cells selected
  have tag : loaded.1.read (activeRead cells) = .bit true :=
    (ConstantWord.constantWord_fold_read_other cells.halfPower
      (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) (activeRead cells)
      (fun member => separate (List.mem_singleton.mp member)) selected).trans
        (even_flag cells store)
  have payload : (loaded.1.read (halfRead cells)).toNat = 2 :=
    (ConstantWord.constantWord_read cells.halfPower 2 selected).trans
      (Nat.mod_eq_of_lt (larger.trans_le source.register_fits))
  refine (packOutput_result cells output loaded.1).trans ?_
  rw [tag, payload]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
