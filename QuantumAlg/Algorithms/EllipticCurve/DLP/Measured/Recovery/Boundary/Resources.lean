/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Independent allowances at both native section boundaries

Every syntactic path is included. The first section pays for its original
reset/readout/check and the following reset. A reused section has no leading
reset but fits the same independently parameterized envelope. Classical
recovery scratch is reused beside all public and persistent storage.

The caller's entire borrowed observation, including its Reference, is restored without
any admission, initialization or positive-path premise. The native carrier is named by
Boundary.sectionCtx; old carrier equations are not silently reused.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model
private abbrev QuantumModel : ExecutionModel := .quantum AlgorithmGate.model .empty

private lemma selected_placed_pool_le {localCtx caller : RuntimeCtx .quantum}
    (placement : ContextEmbedding localCtx caller)
    (code : Circuit QuantumModel localCtx localCtx false) (pool : ResourcePool QuantumModel)
    (bound : ∀ path, code.resourcePool path ≤ pool)
    (path : (BitWord.selectForCircuit
      (Circuit.embed (allowAllocation := false) placement code)).Path) :
    (BitWord.selectForCircuit
      (Circuit.embed (allowAllocation := false) placement code)).resourcePool path ≤
        BitWord.liftQuantumPool pool := by
  apply Events.selected_pool_le
  intro childPath
  rw [Circuit.resourcePool_embed]
  exact bound childPath

private lemma persistent_child_pool_le {ctx : RuntimeCtx .quantum}
    (code : Circuit Model ctx ctx false) (pool : ResourcePool Model)
    (bounded : ∀ path : code.Path, code.resourcePool path ≤ pool)
    (width scalarWidth : Nat)
    (path : (sampleUnderPersistent (model := Model) (ctx := ctx) code width scalarWidth).Path) :
    (sampleUnderPersistent (model := Model) (ctx := ctx) code width scalarWidth).resourcePool
      path ≤ pool :=
  (candidateCheck_sampleUnderPersistent_resourcePool (model := Model) (ctx := ctx)
    code width scalarWidth path).le.trans (bounded path)

private lemma owned_run_restores {ctx : RuntimeCtx .quantum} {shape : CShape}
    (run : AlgorithmRun Model ctx ctx shape true)
    (noBorrowed : ctx.borrowedQuantumWires = [])
    {Reference : Register} (input : OracleInput .empty ctx Reference) :
    run.RestoresBorrowed environment input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit (model := Model)
    (pre := ctx) (post := ctx) (shape := shape) (allowAllocation := true) run environment ?_ input
  intro Reference History _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment) (model := Model)
    (pre := ctx) (post := ctx) (allowAllocation := true) run.code noBorrowed Reference state

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

/-- Every physical reset measurement and its possible X correction are independently charged. -/
def resetBudget (width : Nat) : ResourcePool QuantumModel :=
  Recovery.PublicInput.Allocation.Events.bankWidth width • Recovery.Initialization.Events.wireBudget

/-- The common completed-section envelope retains native checker and next-reset charges. -/
def sectionBudget (nontrivial : 2 ≤ problem.order) : ResourcePool Model :=
  (BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem)) +
    attemptEnvelope Model (ECDLP.Canonical.Layout.curveSpec E)
      (Canonical.resourceModulusSpec problem nontrivial)) +
    BitWord.liftQuantumPool (resetBudget p.size)

/-- Count-independent live storage includes the exact original recovery/final-option maximum. -/
def sectionResources (nontrivial : 2 ≤ problem.order) : ResourceBudget Model where
  events := sectionBudget E problem nontrivial
  resident := recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth problem) + (sectionCtx E problem).residentSpace
  auxiliary := recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
      (orderWidth problem) + (sectionCtx E problem).auxiliarySpace

/-- The same independent whole-section unit envelope bounds quantum dependency time. -/
def sectionTimeLimit (nontrivial : 2 ≤ problem.order) : Nat :=
  ResourcePool.weightedCount (fun _ => 1) (sectionBudget E problem nontrivial)

private lemma reset_native_pool_le
    (path : (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).Path) :
    (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).resourcePool path ≤
      resetBudget p.size := by
  have budget : (Recovery.Layout.terminal p.size (orderWidth problem)).systemCount •
      Recovery.Initialization.Events.wireBudget = resetBudget p.size :=
    congrArg (fun count : Nat =>
      count • (Recovery.Initialization.Events.wireBudget : ResourcePool QuantumModel))
        (Events.terminal_systemCount p.size (orderWidth problem))
  exact (Recovery.Initialization.Events.newReset_budget E fieldTail
    (orderWidth problem) seed path).trans_eq budget

private lemma resetChild_pool_le
    (path : (resetChild E fieldTail problem seed).Path) :
    (resetChild E fieldTail problem seed).resourcePool path ≤
      BitWord.liftQuantumPool (resetBudget p.size) := by
  exact selected_placed_pool_le
    (localCtx := Recovery.Layout.terminal p.size (orderWidth problem))
    (caller := Recovery.PublicInput.context E (orderWidth problem))
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed)
    (resetBudget p.size) (reset_native_pool_le E fieldTail problem seed) path

private lemma reset_pool_le
    (path : (reset E fieldTail problem seed).Path) :
    (reset E fieldTail problem seed).resourcePool path ≤
      BitWord.liftQuantumPool (resetBudget p.size) :=
  persistent_child_pool_le (ctx := Recovery.PublicInput.context E (orderWidth problem))
    (resetChild E fieldTail problem seed) (BitWord.liftQuantumPool (resetBudget p.size))
    (resetChild_pool_le E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) path

private lemma readout_pool_le
    (path : (readoutChild E problem points r coefficient).Path) :
    (readoutChild E problem points r coefficient).resourcePool path ≤
      BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem)) := by
  apply selected_placed_pool_le
  intro childPath
  have bounded := Recovery.Conversion.Events.convertedStages_original_gateBudget
    E problem r points coefficient childPath
  exact (Multiset.le_add_left _ _).trans
    (bounded.trans (Multiset.le_add_right _ _))

private lemma attempt_pool_le (nontrivial : 2 ≤ problem.order)
    (path : (attempt E fieldTail problem points seed r coefficient nontrivial).Path) :
    (attempt E fieldTail problem points seed r coefficient nontrivial).resourcePool path ≤
      BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem)) +
        attemptEnvelope Model (ECDLP.Canonical.Layout.curveSpec E)
          (Canonical.resourceModulusSpec problem nontrivial) :=
  sampledAttempt_pool_le (round E fieldTail problem points seed r coefficient)
    (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) _
    (Events.round_budget E fieldTail problem points seed r coefficient) path

private lemma body_pool_le (nontrivial : 2 ≤ problem.order)
    (path : (body E problem points r coefficient nontrivial).Path) :
    (body E problem points r coefficient nontrivial).resourcePool path ≤
      BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem)) +
        attemptEnvelope Model (ECDLP.Canonical.Layout.curveSpec E)
          (Canonical.resourceModulusSpec problem nontrivial) :=
  sampledAttempt_pool_le (readoutChild E problem points r coefficient)
    (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) _
    (readout_pool_le E problem points r coefficient) path

/-- The first section charges both real resets and the complete actual sampled attempt. -/
lemma first_pool_le (nontrivial : 2 ≤ problem.order)
    (path : (first E fieldTail problem points seed r coefficient nontrivial).Path) :
    (first E fieldTail problem points seed r coefficient nontrivial).resourcePool path ≤
      sectionBudget E problem nontrivial := by
  let equivalent := (first_equiv E fieldTail problem points seed r coefficient nontrivial).symm
  have same := congrArg ResourcePool.ofList (equivalent.events path)
  change (first E fieldTail problem points seed r coefficient nontrivial).resourcePool path = _
    at same
  rw [same]
  change ResourcePool.ofList
    ((attempt E fieldTail problem points seed r coefficient nontrivial).eventTrace
      (equivalent.path path).1 ++
      (reset E fieldTail problem seed).eventTrace (equivalent.path path).2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (attempt_pool_le E fieldTail problem points seed r coefficient
    nontrivial (equivalent.path path).1)
    (reset_pool_le E fieldTail problem seed (equivalent.path path).2)

/-- The reused section omits the leading reset and satisfies the common complete envelope. -/
lemma reused_pool_le (nontrivial : 2 ≤ problem.order)
    (path : (reused E fieldTail problem points seed r coefficient nontrivial).Path) :
    (reused E fieldTail problem points seed r coefficient nontrivial).resourcePool path ≤
      sectionBudget E problem nontrivial := by
  change ResourcePool.ofList
    ((body E problem points r coefficient nontrivial).eventTrace path.1 ++
      (reset E fieldTail problem seed).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (body_pool_le E problem points r coefficient nontrivial path.1)
    (reset_pool_le E fieldTail problem seed path.2)

/-- Both complete sections meet their time limit on their same actual paths. -/
lemma section_depth_certificate (nontrivial : 2 ≤ problem.order) :
    (∀ path, (first E fieldTail problem points seed r coefficient nontrivial).quantumTime path ≤
      sectionTimeLimit E problem nontrivial) ∧
    (∀ path, (reused E fieldTail problem points seed r coefficient nontrivial).quantumTime path ≤
      sectionTimeLimit E problem nontrivial) := by
  constructor
  · intro path
    exact (Circuit.quantumTime_le_unitDepth _ path).trans
      (Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path
        (first_pool_le E fieldTail problem points seed r coefficient nontrivial path))
  · intro path
    exact (Circuit.quantumTime_le_unitDepth _ path).trans
      (Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path
        (reused_pool_le E fieldTail problem points seed r coefficient nontrivial path))

private lemma sample_reset_space {ctx : RuntimeCtx .quantum}
    (sampleCode resetCode : Circuit Model ctx ctx false) {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (path : ((sampledAttempt sampleCode curve modulus sample base target).seq
      (sampleUnderPersistent resetCode width scalarWidth)).Path) :
    ((sampledAttempt sampleCode curve modulus sample base target).seq
      (sampleUnderPersistent resetCode width scalarWidth)).peakResidentSpace path ≤
        recoveryTailScratchSpace .quantum width scalarWidth +
          (persistentCtx ctx width scalarWidth).residentSpace ∧
    ((sampledAttempt sampleCode curve modulus sample base target).seq
      (sampleUnderPersistent resetCode width scalarWidth)).peakAuxiliarySpace path ≤
        recoveryTailScratchSpace .quantum width scalarWidth +
          (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  constructor
  · refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · exact (sampledAttempt_resident_le sampleCode curve modulus sample base target path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (candidateCheck_sampleUnderPersistent_resident resetCode width scalarWidth
        path.2).le.trans (fun _ => Nat.le_add_left _ _)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · exact (sampledAttempt_auxiliary_le sampleCode curve modulus sample base target path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (candidateCheck_sampleUnderPersistent_auxiliary resetCode width scalarWidth
        path.2).le.trans (fun _ => Nat.le_add_left _ _)

/-- Both sections retain every public/persistent cell and the reused native scratch allowance. -/
lemma section_space_certificate (nontrivial : 2 ≤ problem.order) :
    (∀ path,
      (first E fieldTail problem points seed r coefficient nontrivial).peakResidentSpace path ≤
          (sectionResources E problem nontrivial).resident ∧
        (first E fieldTail problem points seed r coefficient nontrivial).peakAuxiliarySpace path ≤
          (sectionResources E problem nontrivial).auxiliary) ∧
    (∀ path,
      (reused E fieldTail problem points seed r coefficient nontrivial).peakResidentSpace path ≤
          (sectionResources E problem nontrivial).resident ∧
        (reused E fieldTail problem points seed r coefficient nontrivial).peakAuxiliarySpace path ≤
          (sectionResources E problem nontrivial).auxiliary) := by
  constructor
  · intro path
    let equivalent := (first_equiv E fieldTail problem points seed r coefficient nontrivial).symm
    rw [equivalent.resident path, equivalent.auxiliary path]
    exact sample_reset_space (round E fieldTail problem points seed r coefficient)
      (resetChild E fieldTail problem seed) (ECDLP.Canonical.Layout.curveSpec E)
      (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) (equivalent.path path)
  · intro path
    exact sample_reset_space (readoutChild E problem points r coefficient)
      (resetChild E fieldTail problem seed) (ECDLP.Canonical.Layout.curveSpec E)
      (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) path

/-- Arbitrary Reference extensions retain the entire original borrowed observation at both cuts. -/
lemma section_borrowed_certificate (nontrivial : 2 ≤ problem.order)
    {Reference : Register} (input : OracleInput .empty (sectionCtx E problem) Reference) :
    (firstRun E fieldTail problem points seed r coefficient nontrivial).RestoresBorrowed
      environment input ∧
      (reusedRun E fieldTail problem points seed r coefficient nontrivial).RestoresBorrowed
        environment input := by
  have noBorrowed : (sectionCtx E problem).borrowedQuantumWires = [] :=
    (Circuit.borrowedQuantumWires_preserved («prefix» E problem)).trans
      (show (Recovery.PublicInput.frame E (orderWidth problem)).borrowedQuantumWires = [] from rfl)
  constructor
  · exact owned_run_restores (ctx := sectionCtx E problem)
      (shape := .product .bit (.unsignedWord (orderWidth problem)))
      (firstRun E fieldTail problem points seed r coefficient nontrivial) noBorrowed input
  · exact owned_run_restores (ctx := sectionCtx E problem)
      (shape := .product .bit (.unsignedWord (orderWidth problem)))
      (reusedRun E fieldTail problem points seed r coefficient nontrivial) noBorrowed input

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
