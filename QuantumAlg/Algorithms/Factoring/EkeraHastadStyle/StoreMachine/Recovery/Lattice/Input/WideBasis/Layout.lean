/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Representation
import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Original actual wide decoder and source-basis allocation

Both original terminal decoder packages and all original raw basis identities
are retained at the source coordinate width. Cross-stage separation and the
complete original thirteen-write footprint are stated in actual storage keys.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix

open Execution
open ClassicalRoutines

noncomputable section

/-- The raw-word width shared with the width-generic lattice state. -/
abbrev Width (N : Nat) : Nat :=
  RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)

/-- Caller-owned references for the decoder--basis initialization prefix. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair stage. -/
  pair : BatchMachine.PairRefs ctx N
  /-- Nested references for the raw stage. -/
  raw : LatticeLoading.RawOutputRefs ctx (Width N)
  roles : LatticeRepresentation.WorkspaceRoles raw

/-- Storage keys written by the two terminal decoders. -/
def decoderKeys {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (pair : BatchMachine.PairRefs ctx N) : List StorageKey :=
  [pair.first.full.toCStorageRef.key,
    pair.first.scratch.toCStorageRef.key,
    pair.first.j.toCStorageRef.key,
    pair.first.k.toCStorageRef.key,
    pair.second.full.toCStorageRef.key,
    pair.second.scratch.toCStorageRef.key,
    pair.second.j.toCStorageRef.key,
    pair.second.k.toCStorageRef.key]

/-- Storage keys of the nine raw basis cells. -/
def rawKeys {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (raw : LatticeLoading.RawOutputRefs ctx width) : List StorageKey :=
  [raw.b11.toCStorageRef.key,
    raw.b12.toCStorageRef.key,
    raw.b13.toCStorageRef.key,
    raw.b21.toCStorageRef.key,
    raw.b22.toCStorageRef.key,
    raw.b23.toCStorageRef.key,
    raw.b31.toCStorageRef.key,
    raw.b32.toCStorageRef.key,
    raw.b33.toCStorageRef.key]

/-- Storage keys that the prefix may modify. -/
def writtenKeys {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : List StorageKey :=
  decoderKeys refs.pair ++
    [refs.raw.b11.toCStorageRef.key,
      refs.raw.b12.toCStorageRef.key,
      refs.raw.b13.toCStorageRef.key,
      refs.raw.b21.toCStorageRef.key,
      refs.raw.b32.toCStorageRef.key]

/-- Local and cross-stage non-aliasing required by the prefix. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  decoder : BatchMachine.PairSeparation refs.pair
  basis : LatticeBasis.Separation refs.pair refs.raw
  decoderRaw : ∀ key ∈ decoderKeys refs.pair,
    ∀ rawKey ∈ rawKeys refs.raw, key ≠ rawKey

/-- The two pure samples selected by the terminal inputs before decoding. -/
def sourceSamples {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before : Store ctx) :
    RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) :=
  (BatchMachine.sourceSample N before (BatchMachine.terminalInput refs.pair.first),
    BatchMachine.sourceSample N before (BatchMachine.terminalInput refs.pair.second))

/-- The raw source basis determined by `sourceSamples`. -/
def sourceBasis {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before : Store ctx) :
    NumberTheory.IntegerBasis3 :=
  RSA.shortLogLatticeBasis (shortLogBits N) (tradeoffBits N)
    (sourceSamples refs before)

/-- Only the four unmodified original basis coordinates require incoming raw zero values. -/
def BasisInitialZero {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (before : Store ctx) (refs : Refs ctx N) : Prop := LatticeBasis.InitialZeros refs.raw before

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
