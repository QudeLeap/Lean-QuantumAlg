/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Spec

/-!
# Independent final checked-attempt protocol

The final readout/check starts from the previous physical reset and has no
following reset. The original generic ECC outcome specifies no final purity
or zero-state promise; the terminal protocol likewise leaves live quantum
output unrestricted while preserving the complete borrowed interface.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- A final sample/readout and checked recovery, without charging a reset
that the original terminal code does not execute. -/
def terminalCheckedSectionEventBudget :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model) :=
  BitWord.liftQuantumPool (samplingRoundBudget E problem) +
    attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)

/-- The final body reuses the same live bank and scratch allowance. -/
def terminalCheckedSectionResourceBudget :
    ResourceBudget (.quantum AlgorithmGate.model .empty BitWord.model) :=
  { checkedSectionResourceBudget E problem nontrivial with
    events := terminalCheckedSectionEventBudget E problem nontrivial }

/-- The original final checked attempt has no physical reset after its
readout/check. Its result is the actual accepted bit and retained word.

**Input.**
- The public point encodings and selected-word invariant, plus the fixed
  quantum seed established by the preceding physical reset.
**Output.**
- The accepted bit and selected word, bounded and sound when accepted;
  a prior accepted word remains unchanged.
**Resource budget.**
- One sampled readout and checked recovery, with no terminal reset event;
  one persistent bank and successive recovery scratch, and a unit-weighted
  whole-section depth bounded by the same terminal event envelope.
**Success.**
- The corrected one-attempt candidate floor when positive, zero otherwise.
**Source.**
- [PZ03, ecc.tex:448-556] for the measured group-shift construction; the
  checked native costs and corrected floor follow the registered implementation
  and finite-cyclic DLP analysis.
-/
def terminalCheckedSectionProblem
    (_addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : Problem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  valid := checkedSectionInputDomain E problem
  initialization := checkedSectionSeededInitialization E fieldTail sameWidth fits problem
    seed
  accepts := checkedSectionAccepts E problem
  successLB := checkedSectionSuccessLB E problem points seed
  states := []
  resources := terminalCheckedSectionResourceBudget E problem nontrivial
  depth :=
    { duration := fun _ => 1
      limit := ResourcePool.weightedCount (fun _ => 1)
        (terminalCheckedSectionEventBudget E problem nontrivial)
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
