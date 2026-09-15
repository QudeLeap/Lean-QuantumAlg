/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Batch.Values
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import all QuantumAlg.Components.Classical.Word.Split.Correctness
import all QuantumAlg.Components.Classical.Word.Split.Resources

/-!
# Original actual short-log sample decoder allocation

The original stored terminal bits feed the original full-word, scratch,
and two source-register destinations. The pure sample interpretation is tied
to actual store reads; caller separation keeps the original write identities.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution

noncomputable section

/-- Width of the first short-log exponent register. -/
abbrev JWidth (N : Nat) : Nat :=
  ShortDLP.firstBits (registerParameters N)

/-- Width of the second short-log exponent register. -/
abbrev KWidth (N : Nat) : Nat :=
  (registerParameters N).ell

/-- The compiled terminal layout is exactly the concatenation of `j` and `k`. -/
@[simp] theorem measurementBits_eq_jkWidth (N : Nat) :
    measurementBits N = JWidth N + KWidth N :=
  rfl

/-- All caller-owned references for one typed terminal decoder invocation. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- The sealed terminal outcome retained by the sampling layer. -/
  input : CInputRef ctx (.bits (measurementBits N))
  /-- Writable full-register decoded value. -/
  full : CWriteRef ctx (.unsignedWord (measurementBits N))
  fullRole : full.toCStorageRef.role = .workspace ∨
    full.toCStorageRef.role = .retained
  /-- A full-width lexical work word used for the destructive split. -/
  scratch : CWriteRef ctx (.unsignedWord (measurementBits N))
  scratchRole : scratch.toCStorageRef.role = .workspace
  /-- Writable first source register. -/
  j : CWriteRef ctx (.unsignedWord (JWidth N))
  jRole : j.toCStorageRef.role = .workspace ∨
    j.toCStorageRef.role = .retained
  /-- Writable second source register. -/
  k : CWriteRef ctx (.unsignedWord (KWidth N))
  kRole : k.toCStorageRef.role = .workspace ∨
    k.toCStorageRef.role = .retained

/-- Read the retained terminal storage cell as a structural input. -/
def terminalInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : CInputRef ctx (.bits (measurementBits N)) :=
  refs.input

/-- The original input/write exclusions and distinct output identities. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  inputAvoidsFull : refs.full.key ∉ (terminalInput refs).storageKeys
  inputAvoidsScratch : refs.scratch.key ∉ (terminalInput refs).storageKeys
  inputAvoidsJ : refs.j.key ∉ (terminalInput refs).storageKeys
  inputAvoidsK : refs.k.key ∉ (terminalInput refs).storageKeys
  fullAvoidsScratch : refs.scratch.key ≠ refs.full.key
  fullAvoidsJ : refs.j.key ≠ refs.full.key
  fullAvoidsK : refs.k.key ≠ refs.full.key
  scratchAvoidsJ : refs.j.key ≠ refs.scratch.key
  scratchAvoidsK : refs.k.key ≠ refs.scratch.key
  jAvoidsK : refs.k.key ≠ refs.j.key

/-- The stored terminal bits viewed in the pure batch-recovery convention. -/
def sourceBits {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (before : Store ctx)
    (input : CInputRef ctx (.bits (measurementBits N))) :
    BatchRecovery.ShortLogTerminalBits (shortLogBits N) (tradeoffBits N) :=
  fun index => (before.read (.bitsGet input index)).toBool

/-- The pure source-shaped `(j, k)` value expected by later batch recovery. -/
def sourceSample {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (before : Store ctx)
    (input : CInputRef ctx (.bits (measurementBits N))) :=
  BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
    (sourceBits N before input)

/-- The first source component is the high quotient of the full terminal index. -/
theorem sourceSample_fst_val {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (before : Store ctx)
    (input : CInputRef ctx (.bits (measurementBits N))) :
    (sourceSample N before input).1.val =
      (BatchRecovery.decodeFullRegisterIndex (shortLogBits N) (tradeoffBits N)
        (sourceBits N before input)).val / 2 ^ KWidth N := by
  simpa only [sourceSample, KWidth, registerParameters,
    ShortDLP.CompiledMAU.registerParameters] using
    (BatchRecovery.decodeTerminalSample_fst_val (shortLogBits N) (tradeoffBits N)
      (sourceBits N before input))

/-- The second source component is the low remainder of the full terminal index. -/
theorem sourceSample_snd_val {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (before : Store ctx)
    (input : CInputRef ctx (.bits (measurementBits N))) :
    (sourceSample N before input).2.val =
      (BatchRecovery.decodeFullRegisterIndex (shortLogBits N) (tradeoffBits N)
        (sourceBits N before input)).val % 2 ^ KWidth N := by
  simpa only [sourceSample, KWidth, registerParameters,
    ShortDLP.CompiledMAU.registerParameters] using
    (BatchRecovery.decodeTerminalSample_snd_val (shortLogBits N) (tradeoffBits N)
      (sourceBits N before input))

/-- The writable cells owned by one member of a two-sample decoder pair. -/
inductive PairOutputSlot where
  | full
  | scratch
  | j
  | k

/-- The storage key of one writable cell in a decoder invocation. -/
def pairOutputKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : PairOutputSlot → StorageKey
  | .full => refs.full.toCStorageRef.key
  | .scratch => refs.scratch.toCStorageRef.key
  | .j => refs.j.toCStorageRef.key
  | .k => refs.k.toCStorageRef.key

/-- The two independently owned terminal-decoder invocations in one pair. -/
structure PairRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the first stage. -/
  first : Refs ctx N
  /-- Nested references for the second stage. -/
  second : Refs ctx N

/-- The original cross-invocation separation of both actual decoder packages. -/
structure PairSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : PairRefs ctx N) : Prop where
  first : Separation refs.first
  second : Separation refs.second
  firstInputAvoidsSecond : ∀ slot,
    pairOutputKey refs.second slot ∉ (terminalInput refs.first).storageKeys
  secondInputAvoidsFirst : ∀ slot,
    pairOutputKey refs.first slot ∉ (terminalInput refs.second).storageKeys
  firstOutputsAvoidSecond : ∀ firstSlot secondSlot,
    pairOutputKey refs.first firstSlot ≠ pairOutputKey refs.second secondSlot

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
