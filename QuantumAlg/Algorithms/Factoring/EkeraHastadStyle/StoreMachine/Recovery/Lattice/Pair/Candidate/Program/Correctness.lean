/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Prefix

/-!
# Original short-log pair recovery computed by the complete actual circuit
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Original exact recovery result, preserved scan data and every unaffected caller read. -/
structure Outcome (input : Input N) (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  initial : LatticeCandidateSlotOutcome.InitialConditions input generator
    (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair before) refs.scan after
  selected : LatticeCandidateSlotMachine.selectedOption refs.scan.selector.selection after =
    RSA.recoverShortLogFromPair (shortLogBits N) (tradeoffBits N) generator
      (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Original source input assumptions suffice for the actual complete pair-candidate circuit. -/
lemma pairCandidateRecoveryInto_correct (input : Input N) (generator : (ZMod N)ˣ)
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    Outcome input generator refs store (recoveryStep input refs store).1 := by
  rw [recoveryStep_store]
  have prefixFacts := pairCandidatePrefix_correct input generator refs separation store initial
  have scan := LatticeCandidateScanInitialized.initializedScanInto_correct (model := model)
    input generator
    (LatticePairNearestPlaneSavedTarget.sourceSamples refs.pair store) refs.scan
    separation.scan separation.scanFrames (prefixStep input refs store).1 prefixFacts
  refine ⟨scan.initial, scan.selected, ?_⟩
  intro shape other separate
  exact (scan.callerFrame other separate.scan).trans
    (pairCandidatePrefix_callerFrame input refs store other separate)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
