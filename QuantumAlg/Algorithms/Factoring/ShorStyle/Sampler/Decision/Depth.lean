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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Duration of the four unconditional initialization instructions. -/
def initializationDuration (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordUnary .copy width)) +
    (duration (.classicalOperation (.wordBinary .bitXor width)) +
      (duration (.classicalOperation (.wordUnary .increment width)) +
        duration (.classicalOperation (.bit .xor))))

/-- Independent maximum of the actual unit and factor instruction chains. -/
def resultDuration (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  max (duration (.classicalOperation (.wordUnary .copy width)) +
      duration (.classicalOperation (.wordBinary .bitXor width)))
    (duration (.classicalOperation (.wordResize (width + 1) width)) +
      duration (.classicalOperation (.bit .not)))

/-- Native GCD and comparison dependencies before the selected result arm. -/
def acceptedDuration (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordResize width (width + 1))) +
    (NumberTheory.GCD.nativeDepthLimit (width + 1) duration +
      (duration (.classicalOperation (.wordResize width (width + 1))) +
        (duration (.classicalOperation (.wordBinary .equal (width + 1))) +
          resultDuration width duration)))

/-- Independent full-path duration, with the actual rejection and packing operations. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  initializationDuration width duration +
    (max (acceptedDuration width duration)
      (duration (.classicalOperation (.wordBinary .bitXor width))) +
        duration (.classicalOperation (.nominalEncoding (.packProduct width (1 + width)))))

/-- The real result condition selects at most the larger native instruction-chain duration. -/
theorem decisionResult_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event kind → Nat)
    (path : (chooseResult shared scratch gcdResult).Path) :
    (chooseResult shared scratch gcdResult).depth duration path ≤
      resultDuration width duration := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · exact Nat.le_max_right _ _
      · exact Nat.le_max_left _ _

/-- The accepted path includes each real GCD and comparison dependency. -/
theorem decisionAccepted_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event kind → Nat)
    (path : (acceptedBody shared scratch gcdResult).Path) :
    (acceptedBody shared scratch gcdResult).depth duration path ≤
      acceptedDuration width duration := by
  change duration (.classicalOperation (.wordResize width (width + 1))) +
    ((NumberTheory.GCD.lexicalBody
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult).depth
        duration path.2.1 +
      (duration (.classicalOperation (.wordResize width (width + 1))) +
        (duration (.classicalOperation (.wordBinary .equal (width + 1))) +
          (chooseResult shared scratch gcdResult).depth duration path.2.2.2.2))) ≤ _
  exact Nat.add_le_add_left (add_le_add
    (NumberTheory.GCD.gcdLexical_depth_le
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
      duration path.2.1)
    (Nat.add_le_add_left (Nat.add_le_add_left
      (decisionResult_depth_le shared scratch gcdResult duration path.2.2.2.2) _) _)) _

/-- Acceptance selection retains the dependency of its actual chosen branch. -/
theorem decisionAcceptance_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (duration : Resource.Event kind → Nat)
    (path : (chooseAccepted shared scratch gcdResult).Path) :
    (chooseAccepted shared scratch gcdResult).depth duration path ≤
      max (acceptedDuration width duration)
        (duration (.classicalOperation (.wordBinary .bitXor width))) := by
  rcases path with ⟨value, selected⟩
  cases value with
  | bit bit =>
      cases bit
      · exact Nat.le_max_right _ _
      · exact (decisionAccepted_depth_le shared scratch gcdResult duration selected).trans
          (Nat.le_max_left _ _)

/-- The complete actual decision satisfies the independently stated native duration bound. -/
theorem decision_depth_le (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width))
    (duration : Resource.Event kind → Nat)
    (path : (circuit shared scratch gcdResult output).Path) :
    (circuit shared scratch gcdResult output).depth duration path ≤
      nativeDepthLimit width duration := by
  change initializationDuration width duration +
    ((chooseAccepted shared scratch gcdResult).depth duration path.2.1 +
      duration (.classicalOperation (.nominalEncoding (.packProduct width (1 + width))))) ≤ _
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (decisionAcceptance_depth_le shared scratch gcdResult duration path.2.1) _) _

/-- Unit event duration gives an explicit linear bound and counts only the selected result arm. -/
theorem decisionNativeDepthLimit_unit (kind : ProblemKind) (width : Nat) :
    nativeDepthLimit width (fun _ : Resource.Event kind => 1) = 10 * width + 30 := by
  simp only [nativeDepthLimit, initializationDuration, acceptedDuration, resultDuration,
    NumberTheory.GCD.gcdNativeDepthLimit_unit]
  omega

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
