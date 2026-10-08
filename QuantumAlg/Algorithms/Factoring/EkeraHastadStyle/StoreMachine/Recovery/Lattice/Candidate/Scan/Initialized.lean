/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Scan.Fold
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection.Init

/-!
# Actual initialized canonical scan with the original exact pair-recovery result
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanInitialized

open Execution
open LatticeCandidateSlotFrames

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {N m ell : Nat} {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

-- Keep the dependent scan path folded when comparing record projections.
-- The generic record laws supply each observation without materializing that path.
attribute [local irreducible] Circuit.sequenceStoreRecord

/-- Clear the actual persistent latch, then execute every original canonical candidate slot. -/
def initializedScanInto (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)) : Circuit model ctx ctx :=
  .seq (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)

/-- The complete actual store and chronological initialized scan path.
This mathematical record retains the full path without native code extraction. -/
noncomputable def initializedStep (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)) (store : Store ctx) :
    Store ctx × (initializedScanInto input refs).Path :=
  Circuit.sequenceStoreRecord
    (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)
    (LatticeCandidateSelectorInit.clearStep refs.selector.selection)
    (LatticeCandidateScan.scanStep (LatticeCandidateModularSetup.modulusSpec input) refs) store

/-- Project the actual initialized store without expanding the canonical scan path. -/
theorem initializedStep_store (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)) (store : Store ctx) :
    (initializedStep input refs store).1 =
      (LatticeCandidateScan.scanStep (LatticeCandidateModularSetup.modulusSpec input) refs
        (LatticeCandidateSelectorInit.clearStep refs.selector.selection store).1).1 :=
  Circuit.sequenceStoreRecord_store (model := model)
    (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)
    (LatticeCandidateSelectorInit.clearStep refs.selector.selection)
    (LatticeCandidateScan.scanStep (LatticeCandidateModularSetup.modulusSpec input) refs) store

/-- Actual initialization and finite candidate execution retain the complete incoming state. -/
theorem initializedScanInto_execute (input : Input N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (initializedScanInto input refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := initializedStep input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact Circuit.execute_sequenceStoreRecord
    (LatticeCandidateSelectorInit.clearAcceptedInto refs.selector.selection)
    (LatticeCandidateScan.scanInto (LatticeCandidateModularSetup.modulusSpec input) refs)
    (LatticeCandidateSelectorInit.clearStep refs.selector.selection)
    (LatticeCandidateScan.scanStep (LatticeCandidateModularSetup.modulusSpec input) refs)
    (LatticeCandidateSelectorInit.clearAcceptedInto_execute refs.selector.selection)
    (LatticeCandidateScan.scanInto_execute (LatticeCandidateModularSetup.modulusSpec input) refs)
    Reference state

/-- Original exact source recovery, unchanged external entry values and complete caller frame. -/
structure Outcome (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx) : Prop where
  initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs after
  selected : LatticeCandidateSlotMachine.selectedOption refs.selector.selection after =
    RSA.recoverShortLogFromPair m ell generator samples
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Actual latch initialization and all original checks compute the source pair recovery. -/
theorem initializedScanInto_correct (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (separation : LatticeCandidateSlotMachine.Separation refs)
    (frameSeparation : FrameSeparation refs) (store : Store ctx)
    (initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs store) :
    Outcome input generator samples refs store (initializedStep input refs store).1 := by
  rw [initializedStep_store]
  let cleared := (LatticeCandidateSelectorInit.clearStep refs.selector.selection store).1
  have clearInitial : LatticeCandidateSlotOutcome.InitialConditions
      input generator samples refs cleared :=
    LatticeCandidateSlotOutcome.initialConditions_transport input generator samples refs
      store cleared initial fun source =>
        LatticeCandidateSelectorInit.clearAcceptedInto_callerFrame refs.selector.selection store
          (externalSourceInput refs source)
          (frameSeparation.externalAvoids source (.selection .accepted))
  have scan := LatticeCandidateScanFold.scanInto_correct (model := model)
    input generator samples refs separation frameSeparation cleared clearInitial
  have empty : LatticeCandidateSlotMachine.selectedOption
      refs.selector.selection cleared = none := by
    unfold LatticeCandidateSlotMachine.selectedOption
    rw [LatticeCandidateSelectorInit.clearAcceptedInto_correct refs.selector.selection store]
    rfl
  refine ⟨scan.initial, ?_, ?_⟩
  · exact LatticeCandidateScanFold.Outcome.recoverShortLogFromPair_of_none
      input generator samples refs cleared _ scan empty
  · intro shape other avoids
    exact (scan.callerFrame other avoids).trans
      (LatticeCandidateSelectorInit.clearAcceptedInto_callerFrame refs.selector.selection
        store other (avoids.selector (.selection .accepted) (by trivial)))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateScanInitialized
