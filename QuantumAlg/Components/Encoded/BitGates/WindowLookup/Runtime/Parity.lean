/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity

/-!
# Paid mask parity from actual runtime table bits

Every table bit is read structurally from an existing unsigned word. Each
contribution executes a real AND into one supplied temporary classical bit,
then a real XOR into the supplied parity bit. The table does not determine
the circuit constructors. The two writable bits and every input cell are
part of the caller's existing context.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel} {width : Nat}

/-- Convert the word's structural MSB position to the measured mask's LSB position. -/
def wordBit (source : CInputRef ctx (.unsignedWord width)) (index : Fin width) :
    CInputRef ctx .bit := .wordBitGet source index.rev

/-- This is a structural read of exactly the original table bit, without arithmetic. -/
lemma wordBit_read (source : CInputRef ctx (.unsignedWord width)) (index : Fin width)
    (store : Store ctx) :
    (store.read (wordBit source index)).toBool = (store.read source).toNat.testBit index.val := by
  change ((store.read source).wordBitGet index.rev).toBool = _
  cases stored : store.read source with
  | unsignedWord encodingValue =>
      change encodingValue.val.testBit (width - 1 - index.rev.val) =
        encodingValue.val.testBit index.val
      congr 1
      rw [Fin.val_rev]
      omega

/-- Every bit of the actual table word is paired with the same original measured position. -/
def inputs (table : CInputRef ctx (.unsignedWord width))
    (measured : CInputRef ctx (.bits width)) : List (CInputRef ctx .bit × CInputRef ctx .bit) :=
  List.ofFn fun index : Fin width => (wordBit table index, .bitsGet measured index)

/-- A real width-one AND writes the measured/table contribution into the supplied temporary bit. -/
def andOp (temporary : CWriteRef ctx .bit) (input : CInputRef ctx .bit × CInputRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product input.1 input.2) temporary

/-- The actual temporary AND result is read by the following paid XOR. -/
def stepProgram (parity temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (MaskParity.instruction (andOp temporary input)).seq
    (MaskParity.instruction (MaskParity.xorOp parity (.storage temporary.toCStorageRef)))

/-- A fixed traversal executes both native instructions for every actual input pair. -/
def foldProgram (parity temporary : CWriteRef ctx .bit) :
    List (CInputRef ctx .bit × CInputRef ctx .bit) →
      Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false
  | [] => .id (model := .quantum AlgorithmGate.model oracles BitWord.model services) ctx
  | input :: rest => (stepProgram parity temporary input).seq (foldProgram parity temporary rest)

/-- Paid clearing and the fixed AND/XOR traversal compute one runtime table-word parity. -/
def program (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (MaskParity.instruction (MaskParity.clearOp parity)).seq (foldProgram parity temporary pairs)

/-- The mathematical parity specification reads the same complete incoming Store. -/
def value (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) (store : Store ctx) : Bool :=
  pairs.foldr (fun input tail =>
    ((store.read input.1).toBool && (store.read input.2).toBool) ^^ tail) false

/-- The true chronological writes of one actual AND/XOR pair. -/
def stepStore (parity temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) (store : Store ctx) : Store ctx :=
  (store.applyOp (andOp temporary input)).applyOp
    (MaskParity.xorOp parity (.storage temporary.toCStorageRef))

/-- The actual pair fold retains every previous write before reading the next pair. -/
def foldStore (parity temporary : CWriteRef ctx .bit) :
    List (CInputRef ctx .bit × CInputRef ctx .bit) → Store ctx → Store ctx
  | [], store => store
  | input :: rest, store => foldStore parity temporary rest (stepStore parity temporary input store)

/-- The actual clear and the same chronological pair writes determine the final Store. -/
def storeStep (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) (store : Store ctx) : Store ctx :=
  foldStore parity temporary pairs (store.applyOp (MaskParity.clearOp parity))

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
