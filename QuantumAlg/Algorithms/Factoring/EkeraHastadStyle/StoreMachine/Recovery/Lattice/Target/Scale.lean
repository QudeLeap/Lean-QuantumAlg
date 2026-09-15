/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Scale.Resources

/-!
# Actual native preimage loading for a centered short-log coordinate

The original structural sample word is expanded into the original supplied
one-bit-wider destination, then shifted left exactly `m` times. This constructs
`2^m * k` without wraparound in the actual interpreter and needs no extra cell.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPreimage

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Read the actual word named by one original writable preimage reference. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Original source word and original destination for the exact preimage `2^m * k`. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (m ell : Nat) where
  k : CInputRef ctx (.unsignedWord ell)
  scaled : CWriteRef ctx (.unsignedWord (ell + m + 1))
  scaledWritable : scaled.toCStorageRef.role = .workspace ∨
    scaled.toCStorageRef.role = .retained

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- Actual original-source resize followed by precisely the prescribed native one-bit shifts. -/
def scaleKInto (refs : Refs ctx m ell) : Circuit ctx ctx :=
  Word.PowerOfTwo.Scale.into m refs.k refs.scaled

/-- Complete actual original preimage store and its native resize-and-shift path. -/
def scaleKStep (refs : Refs ctx m ell) (store : Store ctx) : Store ctx × (scaleKInto refs).Path :=
  Word.PowerOfTwo.Scale.step m refs.k refs.scaled store

/-- Actual native preimage loading retains every incoming state block and original history. -/
theorem scaleKInto_execute (refs : Refs ctx m ell) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scaleKInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((scaleKStep refs entry.1).1, (entry.2, (scaleKStep refs entry.1).2))) :=
  Word.PowerOfTwo.Scale.into_execute m refs.k refs.scaled Reference state

/-- The original output width makes the actual preimage exactly `2^m * k`, without wraparound. -/
theorem scaleKInto_read (refs : Refs ctx m ell) (store : Store ctx) :
    ((scaleKStep refs store).1.read (writeInput refs.scaled)).toNat =
      2 ^ m * (store.read refs.k).toNat :=
  (Word.PowerOfTwo.Scale.into_read m refs.k refs.scaled store (by omega)).trans (Nat.mul_comm _ _)

/-- Every actual read outside the original preimage destination remains exactly unchanged. -/
theorem scaleKInto_callerFrame (refs : Refs ctx m ell) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.scaled.key ∉ other.storageKeys) :
    (scaleKStep refs store).1.read other = store.read other :=
  Word.PowerOfTwo.Scale.into_callerFrame m refs.k refs.scaled store other avoids

/-- Each actual preimage path emits the independent native formula with the original widths. -/
theorem scaleKInto_events (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    (scaleKInto refs).eventTrace path = Word.PowerOfTwo.Scale.scaleTrace ell (ell + m + 1) m :=
  Word.PowerOfTwo.Scale.into_events m refs.k refs.scaled path

/-- Actual preimage multiplicities equal the complete independent native formula. -/
theorem scaleKInto_resourcePool (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    (scaleKInto refs).resourcePool path =
      ResourcePool.ofList (Word.PowerOfTwo.Scale.scaleTrace ell (ell + m + 1) m) :=
  Word.PowerOfTwo.Scale.into_resourcePool m refs.k refs.scaled path

/-- Exact source preimage, complete caller frame and native trace of the actual execution path. -/
theorem scaleKInto_correct (refs : Refs ctx m ell) (store : Store ctx) :
    ((scaleKStep refs store).1.read (writeInput refs.scaled)).toNat =
      2 ^ m * (store.read refs.k).toNat ∧
    (∀ {shape : CShape} (other : CInputRef ctx shape), refs.scaled.key ∉ other.storageKeys →
      (scaleKStep refs store).1.read other = store.read other) ∧
    (scaleKInto refs).eventTrace (scaleKStep refs store).2 =
      Word.PowerOfTwo.Scale.scaleTrace ell (ell + m + 1) m :=
  ⟨scaleKInto_read refs store, scaleKInto_callerFrame refs store,
    scaleKInto_events refs (scaleKStep refs store).2⟩

/-- Actual preimage loading executes exactly one resize and the prescribed number of shifts. -/
theorem scaleKInto_eventCount (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    ((scaleKInto refs).eventTrace path).length = m + 1 :=
  Word.PowerOfTwo.Scale.into_eventCount m refs.k refs.scaled path

/-- Actual preimage loading has the exact serial native resize-and-shift unit-duration depth. -/
theorem scaleKInto_depth (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    (scaleKInto refs).depth (fun _ => 1) path = m + 1 :=
  Word.PowerOfTwo.Scale.into_depth m refs.k refs.scaled path

/-- Actual preimage loading restores every borrowed-reference correlation jointly. -/
theorem scaleKInto_borrowedRestored (refs : Refs ctx m ell) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scaleKInto refs).BorrowedRestored Reference state
      ((scaleKInto refs).execute Reference state) :=
  Word.PowerOfTwo.Scale.into_borrowedRestored m refs.k refs.scaled Reference state

/-- Every actual preimage instruction retains the complete original context. -/
theorem scaleKInto_visited (refs : Refs ctx m ell) (path : (scaleKInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (scaleKInto refs).visitedContexts path) :
    visited = ctx :=
  Word.PowerOfTwo.Scale.into_visited m refs.k refs.scaled path visited present

/-- All original resident entries remain counted throughout actual preimage loading. -/
theorem scaleKInto_resident_le (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    (scaleKInto refs).peakResidentSpace path ≤ ctx.residentSpace :=
  Word.PowerOfTwo.Scale.into_resident_le m refs.k refs.scaled path

/-- All original auxiliary roles remain counted throughout actual preimage loading. -/
theorem scaleKInto_auxiliary_le (refs : Refs ctx m ell) (path : (scaleKInto refs).Path) :
    (scaleKInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  Word.PowerOfTwo.Scale.into_auxiliary_le m refs.k refs.scaled path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPreimage
