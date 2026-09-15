/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics

/-!
# Full-state semantics of the actual recovery and selection tail

The same actual attempt and selector records compose in increasing sample
order. Every quantum-reference block and old history follows this complete
store map. The four real initializations and releases enclose the loop and its
single final optional pack; no success or initial-store certificate is supplied.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum}

/-- The original stored selector is reached through the complete actual attempt record. -/
theorem selectAttempt_actualRecord (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width) :
    ∃ record : Store ctx → Store ctx × (selectAttempt P input target refs).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (selectAttempt P input target refs).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  exact withAttempt_actualRecord P input target _ (fun candidate accepted transport =>
    ⟨FirstAccepted.step ⟨accepted, candidate⟩ (liftSelector refs transport),
      FirstAccepted.firstAccepted_execute ⟨accepted, candidate⟩ (liftSelector refs transport)⟩)

/-- Choose the witnessed actual store and path map of one full attempt. -/
def selectionAttemptRecord (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width) :
    Store ctx → Store ctx × (selectAttempt P input target refs).Path :=
  Classical.choose (selectAttempt_actualRecord P input target refs)

/-- The chosen record is witnessed by the full interpreter equation on every reference block. -/
theorem selectionAttemptRecord_execute (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selectAttempt P input target refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((selectionAttemptRecord P input target refs entry.1).1,
          (entry.2, (selectionAttemptRecord P input target refs entry.1).2))) :=
  Classical.choose_spec (selectAttempt_actualRecord P input target refs) Reference state

/-- The actual loop records every attempt on the store returned by its predecessor. -/
def selectionLoopRecord (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width) :
    Store ctx → Store ctx × (selectionLoop P count samples target refs).Path :=
  Circuit.forRangeRecord count (fun index => selectAttempt P (samples index) target refs)
    (fun index => selectionAttemptRecord P (samples index) target refs)

/-- The full actual loop retains all quantum-reference blocks and the incoming history. -/
theorem selectionLoop_execute (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selectionLoop P count samples target refs).execute Reference state =
      state.mapClassical (fun entry =>
        ((selectionLoopRecord P count samples target refs entry.1).1,
          (entry.2, (selectionLoopRecord P count samples target refs entry.1).2))) :=
  Circuit.execute_forRangeRecord count _ _
    (fun index => selectionAttemptRecord_execute P (samples index) target refs) Reference state

/-- Every actual attempt contributes to the chronological complete-store fold. -/
theorem selectionLoopRecord_store (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (store : Store ctx) :
    (selectionLoopRecord P count samples target refs store).1 =
      (List.ofFn (fun index => fun current =>
        (selectionAttemptRecord P (samples index) target refs current).1)).foldl
          (fun current update => update current) store :=
  Circuit.forRangeRecord_store count _ _ store

private def packRecord {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    Store ctx × (Circuit.classical (selectionPack refs output)).Path :=
  (store.applyOp (selectionPack refs output), ())

private theorem pack_execute {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.classical (selectionPack refs output)).execute Reference state =
      state.mapClassical (fun entry =>
        ((packRecord refs output entry.1).1,
          (entry.2, (packRecord refs output entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The original pack is the final real instruction in the complete recovery record. -/
def recoveryBodyRecord (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) :
    Store ctx → Store ctx × (recoveryBody P count samples target refs output).Path :=
  Circuit.sequenceRecord _ _ (selectionLoopRecord P count samples target refs)
    (packRecord refs output)

/-- The same complete state executes the entire actual loop and final pack. -/
theorem groupRecoveryBody_execute (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (recoveryBody P count samples target refs output).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryBodyRecord P count samples target refs output entry.1).1,
          (entry.2, (recoveryBodyRecord P count samples target refs output entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (selectionLoop_execute P count samples target refs)
    (pack_execute refs output) Reference state

/-- The final store is exactly the actual loop store followed by the single optional write. -/
theorem groupRecoveryBodyRecord_store (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) (store : Store ctx) :
    (recoveryBodyRecord P count samples target refs output store).1 =
      (selectionLoopRecord P count samples target refs store).1.applyOp
        (selectionPack refs output) := rfl

/-- Four real initializations and releases surround the same complete loop and pack record. -/
theorem groupRecoveryInto_actualRecord (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) :
    ∃ record : Store ctx → Store ctx × (recoveryInto P count samples target output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (recoveryInto P count samples target output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  obtain ⟨record, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post ctx (selectorShapes P.width)
      (fun cells _ transport _ =>
        recoveryBody P count (fun index => transport.liftInput (samples index))
          (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output))
      (fun _ _ => True) (by
        intro inner cells distinct transport separated
        exact ⟨recoveryBodyRecord P count (fun index => transport.liftInput (samples index))
          (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output),
          groupRecoveryBody_execute P count (fun index => transport.liftInput (samples index))
            (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output),
          by intros; trivial⟩)
  exact ⟨record, equation⟩

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
