/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Layout

/-!
# Actual decoding of a stored short-log terminal sample

The actual stored bits first feed the native shift-and-append decoder. Its
actual full word is copied to the original scratch word, then split into the
original source-shaped high and low registers by native resize and shift gates.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Original full-register bit convention, read from the actual retained classical source. -/
def decoderInputs (refs : Refs ctx N) (index : Fin (measurementBits N)) : CInputRef ctx .bit :=
  .bitsGet (terminalInput refs) (Fin.rev index)

/-- Actual native full-word decoding in the original terminal bit order. -/
def fullDecodeInto (refs : Refs ctx N) : Circuit ctx ctx :=
  TerminalDecode.intoFromBitRefs .littleEndian (decoderInputs refs) refs.full

/-- The actual full-word store and chronological decoded-bit path. -/
def fullDecodeStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (fullDecodeInto refs).Path :=
  TerminalDecode.foldStep refs.full
    (List.ofFn (fun index => decoderInputs refs (TerminalDecode.sourceIndex .littleEndian index)))
    store

/-- The original low/high split shares the original work and output identities. -/
abbrev splitRefs (refs : Refs ctx N) : Word.Split.Refs ctx (JWidth N) (KWidth N) where
  work := refs.scratch
  high := refs.j
  low := refs.k

/-- Actual resize/shift/resize splitting of the original full-width work word. -/
def splitFullInto (refs : Refs ctx N) : Circuit ctx ctx := Word.Split.splitInto (splitRefs refs)

/-- Actual native split store and path, using the reusable word-split interpreter equation. -/
def splitFullStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (splitFullInto refs).Path := Word.Split.splitStep (splitRefs refs) store

/-- The actual decoded full word is copied into the original destructive working cell. -/
def copyOp (refs : Refs ctx N) :
    ClassicalOp (.unsignedWord (measurementBits N)) (.unsignedWord (measurementBits N)) ctx ctx :=
  .wordUnary .copy (measurementBits N) ctx (.storage refs.full.toCStorageRef) refs.scratch

/-- Original copy followed by the actual native work-word split. -/
def copySplitInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (.classical (copyOp refs)) (splitFullInto refs)

/-- The actual copied word feeds the actual split store and path. -/
def copySplitStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (copySplitInto refs).Path :=
  let split := splitFullStep refs (store.applyOp (copyOp refs))
  (split.1, ((), split.2))

/-- Actual stored terminal bits materialize the original full word and source-shaped pair. -/
def decodeInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (fullDecodeInto refs) (copySplitInto refs)

/-- Actual final decoder store and complete chronological bit-decoding and splitting path. -/
def decodeStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (decodeInto refs).Path :=
  let decoded := fullDecodeStep refs store
  let split := copySplitStep refs decoded.1
  (split.1, (decoded.2, split.2))

/-- Both original terminal outcomes are decoded in sequence on their actual shared store. -/
def decodePairInto (refs : PairRefs ctx N) : Circuit ctx ctx :=
  .seq (decodeInto refs.first) (decodeInto refs.second)

/-- The first actual decoder store feeds the second decoder and retains both original paths. -/
def decodePairStep (refs : PairRefs ctx N) (store : Store ctx) :
    Store ctx × (decodePairInto refs).Path :=
  let first := decodeStep refs.first store
  let second := decodeStep refs.second first.1
  (second.1, (first.2, second.2))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
