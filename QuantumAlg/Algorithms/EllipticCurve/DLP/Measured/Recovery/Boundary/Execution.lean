/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Sequence
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Sequence
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Rotation

/-!
# Concrete native boundaries of the allocated streaming run

The caller is the reduced physical bank beside the original two borrowed
classical points. Seven native cells are allocated once. No old structural
compiler or old allocating sampling child is reconstructed here.

The actual attempt remains the Run4 attempt. Its decomposition is an explicit
OperationalEquiv with the same complete Store, service, Reference and history,
and all six path/resource fields. It is not an equality of Circuit trees.
First and reused nonterminal sections differ by exactly the initial reset.
The final body and the finite range's final identity remain in rotatedTail.


-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

/-- The actual reduced bank and borrowed public points, beside the same seven cells. -/
abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The original Run4 reset, selected and placed without an allocation permission. -/
def resetChild : Circuit Model (Recovery.PublicInput.context E (orderWidth problem))
    (Recovery.PublicInput.context E (orderWidth problem)) false :=
  BitWord.selectForCircuit (Circuit.embed (allowAllocation := false)
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed))

/-- The original converted stream, with no repeated leading reset. -/
def readoutChild : Circuit Model (Recovery.PublicInput.context E (orderWidth problem))
    (Recovery.PublicInput.context E (orderWidth problem)) false :=
  BitWord.selectForCircuit (Circuit.embed (allowAllocation := false)
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
      coefficient))

/-- The actual chronological cells in the original checker's canonical order. -/
def sample : CInputRef (Recovery.PublicInput.context E (orderWidth problem))
    (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2)) :=
  recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))

/-- One original reset beside the seven existing cells. -/
def reset : Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
  sampleUnderPersistent (resetChild E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The complete original checker follows the same converted readout. -/
def body (nontrivial : 2 ≤ problem.order) :
    Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
  sampledAttempt (readoutChild E problem points r coefficient)
    (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))

/-- The unchanged actual Run4 loop body, before any mathematical reassociation. -/
def attempt (nontrivial : 2 ≤ problem.order) :
    Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
  sampledAttempt (round E fieldTail problem points seed r coefficient)
    (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))

/-- The first completed nonterminal section executes both its own and the next reset. -/
def first (nontrivial : 2 ≤ problem.order) :
    Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
  ((reset E fieldTail problem seed).seq (body E problem points r coefficient nontrivial)).seq
    (reset E fieldTail problem seed)

/-- A reused nonterminal section starts after the preceding section's reset. -/
def reused (nontrivial : 2 ≤ problem.order) :
    Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
  (body E problem points r coefficient nontrivial).seq (reset E fieldTail problem seed)

private lemma select_embed {gates : GateModel} {oracles : OracleModel}
    {localCtx caller : RuntimeCtx .quantum} {allowAllocation : Bool}
    (placement : ContextEmbedding localCtx caller)
    (child : Circuit (.quantum gates oracles) localCtx localCtx false) :
    BitWord.selectForCircuit (Circuit.embed (allowAllocation := allowAllocation) placement child) =
      Circuit.embed (allowAllocation := allowAllocation) placement
        (BitWord.selectForCircuit child) := rfl

private def operationalEquiv_endpoints {model : ExecutionModel} {allowAllocation : Bool}
    {pre post : RuntimeCtx model.kind}
    {source placedSource target placedTarget : Circuit model pre post allowAllocation}
    (sourceSame : source = placedSource) (targetSame : target = placedTarget)
    (certificate : Circuit.OperationalEquiv placedSource placedTarget) :
    Circuit.OperationalEquiv source target := by
  cases sourceSame
  cases targetSame
  exact certificate

/-- Public placement distributes semantically over the same selected native children. -/
def round_split : Circuit.OperationalEquiv
    (round E fieldTail problem points seed r coefficient)
    ((resetChild E fieldTail problem seed).seq (readoutChild E problem points r coefficient)) :=
  by
    let placement : ContextEmbedding (Recovery.Layout.terminal p.size (orderWidth problem))
        (Recovery.PublicInput.context E (orderWidth problem)) :=
      Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)
    let resetCode : Circuit (.quantum AlgorithmGate.model .empty)
        (Recovery.Layout.terminal p.size (orderWidth problem))
        (Recovery.Layout.terminal p.size (orderWidth problem)) false :=
      Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed
    let readoutCode : Circuit (.quantum AlgorithmGate.model .empty)
        (Recovery.Layout.terminal p.size (orderWidth problem))
        (Recovery.Layout.terminal p.size (orderWidth problem)) false :=
      Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
        coefficient
    have resetSame : resetChild E fieldTail problem seed =
        Circuit.embed (model := Model) (allowAllocation := false) placement
          (BitWord.selectForCircuit resetCode) :=
      select_embed placement resetCode
    have readoutSame : readoutChild E problem points r coefficient =
        Circuit.embed (model := Model) (allowAllocation := false) placement
          (BitWord.selectForCircuit readoutCode) :=
      select_embed placement readoutCode
    have roundSame : round E fieldTail problem points seed r coefficient =
        Circuit.embed (model := Model) (allowAllocation := false) placement
          ((BitWord.selectForCircuit resetCode).seq (BitWord.selectForCircuit readoutCode)) :=
      (select_embed placement (resetCode.seq readoutCode)).trans
        (congrArg (fun child : Circuit Model
            (Recovery.Layout.terminal p.size (orderWidth problem))
            (Recovery.Layout.terminal p.size (orderWidth problem)) false =>
          Circuit.embed (model := Model) (allowAllocation := false) placement child)
          (BitWord.selectForCircuit_seq resetCode readoutCode))
    exact operationalEquiv_endpoints roundSame
      (congrArg₂ (fun first second : Circuit Model
          (Recovery.PublicInput.context E (orderWidth problem))
          (Recovery.PublicInput.context E (orderWidth problem)) false => first.seq second)
        resetSame readoutSame)
      (Circuit.embed_seqOperationalEquiv (model := Model) (allowAllocation := false) placement
        (BitWord.selectForCircuit resetCode) (BitWord.selectForCircuit readoutCode))

/-- Both placements and original complete checking preserve the complete operational contract. -/
def attempt_split (nontrivial : 2 ≤ problem.order) : Circuit.OperationalEquiv
    (attempt E fieldTail problem points seed r coefficient nontrivial)
    ((reset E fieldTail problem seed).seq (body E problem points r coefficient nontrivial)) :=
  by
    let placement : ContextEmbedding (Recovery.PublicInput.context E (orderWidth problem))
        (sectionCtx E problem) :=
      persistentEmbedding (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    let checking : Circuit Model (sectionCtx E problem) (sectionCtx E problem) :=
      persistentAttempt (model := Model) (ECDLP.Canonical.Layout.curveSpec E)
        (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
        (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
        (Recovery.PublicInput.contextTargetRef E (orderWidth problem))
    have placed : Circuit.OperationalEquiv
        (attempt E fieldTail problem points seed r coefficient nontrivial)
        (sampledAttempt (model := Model)
          ((resetChild E fieldTail problem seed).seq (readoutChild E problem points r coefficient))
          (ECDLP.Canonical.Layout.curveSpec E)
          (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
          (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
          (Recovery.PublicInput.contextTargetRef E (orderWidth problem))) :=
      (Circuit.OperationalEquiv.embed (model := Model) (allowAllocation := true) placement
        (round_split E fieldTail problem points seed r coefficient)).append checking
    exact placed.trans
      (candidateCheck_sampledAttempt_seqOperationalEquiv (model := Model)
        (resetChild E fieldTail problem seed) (readoutChild E problem points r coefficient)
        (ECDLP.Canonical.Layout.curveSpec E)
        (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
        (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
        (Recovery.PublicInput.contextTargetRef E (orderWidth problem)))

/-- The first section is the actual first attempt followed by the next actual reset. -/
def first_equiv (nontrivial : 2 ≤ problem.order) : Circuit.OperationalEquiv
    ((attempt E fieldTail problem points seed r coefficient nontrivial).seq
      (reset E fieldTail problem seed))
    (first E fieldTail problem points seed r coefficient nontrivial) :=
  (attempt_split E fieldTail problem points seed r coefficient nontrivial).append
    (reset E fieldTail problem seed)

/-- The original allocation and seven-cell initialization precede the first native section. -/
def «prefix» : Circuit Model (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E
  problem) :=
  (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).seq
    (retainPersistent (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))

/-- At two or more attempts, expose the first section without dropping a path or final pack. -/
def run_firstBoundary (nontrivial : 2 ≤ problem.order) (count : Nat) :
    Circuit.OperationalEquiv
      (run E fieldTail problem points seed r coefficient nontrivial ((count + 1) + 1)).code
      ((BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth
        problem))).seq
        (((retainPersistent (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).seq
          ((first E fieldTail problem points seed r coefficient nontrivial).seq
            (Circuit.OperationalEquiv.rotatedTail (reset E fieldTail problem seed)
              (body E problem points r coefficient nontrivial) count))).seq
          (packBatchResult (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)))) := by
  let each := attempt_split E fieldTail problem points seed r coefficient nontrivial
  let loop := (Circuit.OperationalEquiv.forRange ((count + 1) + 1)
    (fun _ => attempt E fieldTail problem points seed r coefficient nontrivial)
    (fun _ => (reset E fieldTail problem seed).seq
      (body E problem points r coefficient nontrivial)) (fun _ => each)).trans
        (Circuit.OperationalEquiv.rotateRangeFirstCycle (reset E fieldTail problem seed)
          (body E problem points r coefficient nontrivial) count)
  exact ((loop.prepend (retainPersistent (model := Model)
      (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))).append
    (packBatchResult (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))).prepend
        (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))

/-- The live accepted/selected pair is read without allocating a final option cell. -/
def read : OutputRead (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) :=
  .read (.product (.storage (persistentAccepted _ _ _).toCStorageRef)
    (.storage (persistentSelected _ _ _).toCStorageRef))

/-- The first section's original complete output manifest. -/
def firstRun (nontrivial : 2 ≤ problem.order) :
    AlgorithmRun Model (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) :=
  ⟨first E fieldTail problem points seed r coefficient nontrivial, Output.all _ (read E problem)⟩

/-- The reused section's original complete output manifest. -/
def reusedRun (nontrivial : 2 ≤ problem.order) :
    AlgorithmRun Model (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) :=
  ⟨reused E fieldTail problem points seed r coefficient nontrivial, Output.all _ (read E problem)⟩

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
