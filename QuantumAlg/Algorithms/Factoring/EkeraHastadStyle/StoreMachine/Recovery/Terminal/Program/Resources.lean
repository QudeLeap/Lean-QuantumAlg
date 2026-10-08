/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Pair
import all QuantumAlg.Components.Classical.TerminalDecode.Trace

/-!
# Actual terminal decoder traces, budgets and borrowed restoration

Each selected bit contributes its native shift and selected increment. The
fixed suffix copies the full word, extracts the low word, shifts the scratch
word and extracts the high word. The independent count and depth bounds cover
both complete decoders and count every original context entry throughout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent ordered native formula for copying and splitting one original decoded word. -/
def copySplitTrace (N : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (measurementBits N)))] ++
    Word.Split.splitTrace (JWidth N) (KWidth N)

/-- Independent ordered formula for a sample's selected bits and complete fixed extraction. -/
def decodeTrace (N : Nat) (bits : List Bool) : List (Resource.Event model) :=
  TerminalDecode.bitsTrace (measurementBits N) bits ++ copySplitTrace N

/-- The ordered actual source bits carried by the complete decoder's selected path. -/
def decodeBits (refs : Refs ctx N) (path : (decodeInto refs).Path) : List Bool :=
  TerminalDecode.selectedBits refs.full
    (List.ofFn (fun index => decoderInputs refs (TerminalDecode.sourceIndex .littleEndian index)))
    path.1

/-- Every actual fixed extraction path emits exactly its independent native copy/split formula. -/
theorem copySplitInto_events (refs : Refs ctx N) (path : (copySplitInto refs).Path) :
    (copySplitInto refs).eventTrace path = copySplitTrace N := by
  exact congrArg₂ List.append (BitWord.bitWord_instruction_eventTrace (copyOp refs) path.1)
    (Word.Split.splitInto_events (splitRefs refs) path.2)

/-- Every actual complete decoder path emits the independent selected-bit and extraction formula. -/
theorem decodeInto_events (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).eventTrace path = decodeTrace N (decodeBits refs path) := by
  exact congrArg₂ List.append (TerminalDecode.fold_events _ _ path.1)
    (copySplitInto_events refs path.2)

/-- Actual decoder multiplicities agree with the independent complete selected-bit trace. -/
theorem decodeInto_resourcePool (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).resourcePool path =
      ResourcePool.ofList (decodeTrace N (decodeBits refs path)) :=
  congrArg ResourcePool.ofList (decodeInto_events refs path)

/-- An independent coordinatewise budget includes both bit arms and the complete fixed suffix. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  TerminalDecode.envelope (measurementBits N) + ResourcePool.ofList (copySplitTrace N)

/-- Actual decoder resource multiplicities obey the complete independent coordinatewise envelope. -/
theorem decodeInto_pool_le (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append, copySplitInto_events]
  exact add_le_add
    (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .littleEndian
      (decoderInputs refs) refs.full path.1) le_rfl

/-- The complete fixed extraction has exactly the low width plus three native instructions. -/
theorem copySplitInto_eventCount (refs : Refs ctx N) (path : (copySplitInto refs).Path) :
    ((copySplitInto refs).eventTrace path).length = KWidth N + 3 := by
  change (_ ++ (splitFullInto refs).eventTrace path.2).length = _
  rw [List.length_append]
  have count := Word.Split.splitInto_eventCount (splitRefs refs) path.2
  change 1 + ((Word.Split.splitInto (splitRefs refs)).eventTrace path.2).length = _
  omega

/-- Actual decoding has at most two instructions per measured bit plus the complete extraction. -/
theorem decodeInto_eventCount_le (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    ((decodeInto refs).eventTrace path).length ≤ 2 * measurementBits N + KWidth N + 3 := by
  have headBound := TerminalDecode.fold_eventCount_le refs.full
    (List.ofFn (fun index => decoderInputs refs (TerminalDecode.sourceIndex .littleEndian index)))
    path.1
  simp only [List.length_ofFn] at headBound
  change ((fullDecodeInto refs).eventTrace path.1 ++
    (copySplitInto refs).eventTrace path.2).length ≤ _
  rw [List.length_append, copySplitInto_eventCount]
  change ((fullDecodeInto refs).eventTrace path.1).length ≤ 2 * measurementBits N at headBound
  omega

/-- The complete fixed extraction has the same exact serial depth at unit duration. -/
theorem copySplitInto_depth (refs : Refs ctx N) (path : (copySplitInto refs).Path) :
    (copySplitInto refs).depth (fun _ => 1) path = KWidth N + 3 := by
  change 1 + (Word.Split.splitInto (splitRefs refs)).depth (fun _ => 1) path.2 = _
  have depth := Word.Split.splitInto_depth (splitRefs refs) path.2
  omega

/-- Actual decoder data dependencies obey the full bit-fold and extraction depth bound. -/
theorem decodeInto_depth_le (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).depth (fun _ => 1) path ≤ 2 * measurementBits N + KWidth N + 3 := by
  have headBound := TerminalDecode.terminalDecode_intoFromBitRefs_depth_le .littleEndian
    (decoderInputs refs) refs.full (fun _ => 1) path.1
  change (fullDecodeInto refs).depth (fun _ => 1) path.1 ≤ measurementBits N * (1 + 1) at headBound
  change (fullDecodeInto refs).depth (fun _ => 1) path.1 +
    (copySplitInto refs).depth (fun _ => 1) path.2 ≤ _
  rw [copySplitInto_depth]
  omega

/-- Both actual decoders emit their complete independent traces in their execution order. -/
theorem decodePairInto_events (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    (decodePairInto refs).eventTrace path =
      decodeTrace N (decodeBits refs.first path.1) ++
        decodeTrace N (decodeBits refs.second path.2) := by
  change _ ++ _ = _
  rw [decodeInto_events, decodeInto_events]

/-- Both actual decoder pools obey the sum of the two independent complete envelopes. -/
theorem decodePairInto_pool_le (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    (decodePairInto refs).resourcePool path ≤ eventEnvelope N + eventEnvelope N := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (decodeInto_pool_le refs.first path.1) (decodeInto_pool_le refs.second path.2)

/-- The original pair executes at most twice the complete single-sample native instruction bound. -/
theorem decodePairInto_eventCount_le (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    ((decodePairInto refs).eventTrace path).length ≤
      2 * (2 * measurementBits N + KWidth N + 3) := by
  change ((decodeInto refs.first).eventTrace path.1 ++
    (decodeInto refs.second).eventTrace path.2).length ≤ _
  rw [List.length_append]
  have first := decodeInto_eventCount_le refs.first path.1
  have second := decodeInto_eventCount_le refs.second path.2
  omega

/-- Both actual sample decoders retain their chronological data dependencies in the total depth. -/
theorem decodePairInto_depth_le (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    (decodePairInto refs).depth (fun _ => 1) path ≤
      2 * (2 * measurementBits N + KWidth N + 3) := by
  change (decodeInto refs.first).depth (fun _ => 1) path.1 +
    (decodeInto refs.second).depth (fun _ => 1) path.2 ≤ _
  have first := decodeInto_depth_le refs.first path.1
  have second := decodeInto_depth_le refs.second path.2
  omega

/-- One complete actual decoder restores every borrowed correlation with the original reference. -/
theorem decodeInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodeInto refs).BorrowedRestored Reference state
      ((decodeInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (fullDecodeInto refs) (copySplitInto refs)
  · exact TerminalDecode.fold_borrowedRestored _ _ Reference state
  · exact Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_classical _ _)
      (Word.Split.splitInto_borrowedRestored (splitRefs refs) Reference _)

/-- Both actual sample decoders jointly restore every borrowed entry and external correlation. -/
theorem decodePairInto_borrowedRestored (refs : PairRefs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodePairInto refs).BorrowedRestored Reference state
      ((decodePairInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (decodeInto refs.first) (decodeInto refs.second) state
    (decodeInto_borrowedRestored refs.first Reference state)
    (decodeInto_borrowedRestored refs.second Reference _)

/-- Actual bit decoding, copying and splitting visit only the complete supplied live context. -/
theorem decodeInto_visited (refs : Refs ctx N) (path : (decodeInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (decodeInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (fullDecodeInto refs).visitedContexts path.1 ++
    ([ctx] ++ (splitFullInto refs).visitedContexts path.2.2) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with decode | copy | split
  · exact TerminalDecode.terminalDecode_fold_visited _ _ path.1 visited decode
  · exact copy
  · exact Word.Split.splitInto_visited (splitRefs refs) path.2.2 visited split

/-- Both actual decoder invocations keep every original context entry live throughout. -/
theorem decodePairInto_visited (refs : PairRefs ctx N) (path : (decodePairInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (decodePairInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ _ ++ _ at present
  exact (List.mem_append.mp present).elim
    (decodeInto_visited refs.first path.1 visited) (decodeInto_visited refs.second path.2 visited)

/-- The complete actual single decoder allocates no additional resident storage. -/
theorem decodeInto_resident_le (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [decodeInto_visited refs path visited present]

/-- The complete actual single decoder counts every already-scoped auxiliary role. -/
theorem decodeInto_auxiliary_le (refs : Refs ctx N) (path : (decodeInto refs).Path) :
    (decodeInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [decodeInto_visited refs path visited present]

/-- Both actual sample decoders allocate no additional resident storage. -/
theorem decodePairInto_resident_le (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    (decodePairInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [decodePairInto_visited refs path visited present]

/-- Both actual sample decoders count every original auxiliary entry throughout. -/
theorem decodePairInto_auxiliary_le (refs : PairRefs ctx N) (path : (decodePairInto refs).Path) :
    (decodePairInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [decodePairInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
