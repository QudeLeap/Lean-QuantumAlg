/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Depth

/-!
# Actual native dependency depth of the residue decision

The bound follows the literal sequential dependencies through initialization,
the selected acceptance arm, the native GCD comparison and the final pack.
Each stored conditional contributes only its selected arm's duration. The
independent formula supports arbitrary native event durations and all widths.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Duration of the four unconditional initialization instructions. -/
def initializationDuration (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .copy width))) +
    (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width))) +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .increment width))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.bit .xor)))))

/-- Independent maximum of the actual unit and factor instruction chains. -/
def resultDuration (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  max (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .copy width))) +
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor width))))
    (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))) +
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))))

/-- Native GCD and comparison dependencies before the selected result arm. -/
def acceptedDuration (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + 1)))) +
    (NumberTheory.GCD.nativeDepthLimit (width + 1) duration +
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize width (width + 1)))) +
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .equal (width + 1)))) +
          resultDuration width duration)))

/-- Independent full-path duration, with the actual rejection and packing operations. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  initializationDuration width duration +
    (max (acceptedDuration width duration)
      (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor width)))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packProduct width (1 + width))))))

/-- The real result condition selects at most the larger native instruction-chain duration. -/
theorem decisionResult_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event model → Nat)
    (path : (chooseResult (model := model) shared scratch gcdResult).Path) :
    (chooseResult (model := model) shared scratch gcdResult).depth duration path ≤
      resultDuration width duration := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · change (factorBody (model := model) scratch gcdResult).Path at selected
        change (factorBody (model := model) scratch gcdResult).depth duration selected ≤ _
        rcases selected with ⟨left, right⟩
        simp only [factorBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
        exact Nat.le_max_right _ _
      · change (unitBody (model := model) shared scratch).Path at selected
        change (unitBody (model := model) shared scratch).depth duration selected ≤ _
        rcases selected with ⟨left, right⟩
        simp only [unitBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
        exact Nat.le_max_left _ _

/-- The accepted path includes each real GCD and comparison dependency. -/
theorem decisionAccepted_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event model → Nat)
    (path : (acceptedBody (model := model) shared scratch gcdResult).Path) :
    (acceptedBody (model := model) shared scratch gcdResult).depth duration path ≤
      acceptedDuration width duration := by
  rcases path with ⟨extended, reduced, loaded, compared, selected⟩
  change (Circuit.seq (BitWord.instruction (execution := model) (Proposal.extendOp scratch))
    (Circuit.seq (NumberTheory.GCD.lexicalBody (model := model)
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
      (Circuit.seq (BitWord.instruction (execution := model) (.wordResize width (width + 1) ctx
        (FirstAccepted.cellRead shared.selector.selected) scratch.extended))
        (Circuit.seq (BitWord.instruction (execution := model) (.wordBinary .equal (width + 1) ctx
          (.product (FirstAccepted.cellRead gcdResult)
            (FirstAccepted.cellRead scratch.extended)) scratch.positive))
          (chooseResult (model := model) shared scratch gcdResult))))).depth duration
      (extended, (reduced, (loaded, (compared, selected)))) ≤ _
  simp only [Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left (add_le_add
    (NumberTheory.GCD.gcdLexical_depth_le
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
      duration reduced)
    (Nat.add_le_add_left (Nat.add_le_add_left
      (decisionResult_depth_le shared scratch gcdResult duration selected) _) _)) _

/-- Acceptance selection retains the dependency of its actual chosen branch. -/
theorem decisionAcceptance_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event model → Nat)
    (path : (chooseAccepted (model := model) shared scratch gcdResult).Path) :
    (chooseAccepted (model := model) shared scratch gcdResult).depth duration path ≤
      max (acceptedDuration width duration)
        (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .bitXor width)))) := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · change (BitWord.instruction (execution := model)
          (clearWordOp scratch.candidate)).Path at selected
        change (BitWord.instruction (execution := model)
          (clearWordOp scratch.candidate)).depth duration selected ≤ _
        rw [BitWord.bitWord_instruction_depth]
        exact Nat.le_max_right _ _
      · exact (decisionAccepted_depth_le shared scratch gcdResult duration selected).trans
          (Nat.le_max_left _ _)

/-- The complete actual decision satisfies the independently stated native duration bound. -/
theorem decision_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (duration : Resource.Event model → Nat)
    (path : (circuit (model := model) shared scratch gcdResult output).Path) :
    (circuit (model := model) shared scratch gcdResult output).depth duration path ≤
      nativeDepthLimit width duration := by
  rcases path with ⟨⟨copied, cleared, incremented, tagged⟩, chosen, packed⟩
  change (Circuit.seq (initializeBody (model := model) shared scratch)
    (Circuit.seq (chooseAccepted (model := model) shared scratch gcdResult)
      (BitWord.instruction (execution := model)
        (packOp shared scratch output)))).depth duration
      ((copied, (cleared, (incremented, tagged))), (chosen, packed)) ≤ _
  simp only [initializeBody, Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (decisionAcceptance_depth_le shared scratch gcdResult duration chosen) _) _

/-- Unit event duration gives an explicit linear bound and counts only the selected result arm. -/
theorem decisionNativeDepthLimit_unit (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) :
    nativeDepthLimit width (fun _ : Resource.Event model => 1) = 10 * width + 30 := by
  simp only [nativeDepthLimit, initializationDuration, acceptedDuration, resultDuration,
    NumberTheory.GCD.gcdNativeDepthLimit_unit]
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
