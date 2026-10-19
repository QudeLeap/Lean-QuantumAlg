/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Frame
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Actual allocation charges before the complete first section

The original allocation is paid once. Its peak and the seven retained cells
fit the same independently prescribed section storage envelope, without
charging repeated initialization or omitting any public-point storage.
All bounds apply to every syntactic path. Borrowed restoration retains the
complete classical and Reference observation on arbitrary original inputs.
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

attribute [local irreducible] Nat.size Nat.clog

private lemma persistent_space_mono (ctx : RuntimeCtx .quantum) (width scalarWidth : Nat) :
    ctx.residentSpace ≤ (persistentCtx ctx width scalarWidth).residentSpace ∧
      ctx.auxiliarySpace ≤ (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  constructor
  · rw [persistentCtx_residentSpace]
    exact fun _ => Nat.le_add_left _ _
  · rw [persistentCtx_auxiliarySpace]
    exact fun _ => Nat.le_add_left _ _

private lemma owned_input_restores {origin final : RuntimeCtx .quantum} {shape : CShape}
    (run : AlgorithmRun Model origin final shape)
    (noBorrowed : origin.borrowedQuantumWires = [])
    {Reference : Register} (input : OracleInput .empty origin Reference) :
    run.RestoresBorrowed environment input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit run environment ?_ input
  intro Reference History _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment) run.code
    noBorrowed Reference state

private lemma sequence_pool_le {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind}
    (before : Circuit model origin ctx) (checked : Circuit model ctx ctx)
    (path : (before.seq checked).Path) (beforeBudget checkedBudget : ResourcePool model)
    (beforeEvents : before.resourcePool path.1 ≤ beforeBudget)
    (checkedEvents : checked.resourcePool path.2 ≤ checkedBudget) :
    (before.seq checked).resourcePool path ≤ beforeBudget + checkedBudget := by
  change before.resourcePool path.1 + checked.resourcePool path.2 ≤ _
  exact add_le_add beforeEvents checkedEvents

private lemma sequence_space_le {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind}
    (before : Circuit model origin ctx) (checked : Circuit model ctx ctx)
    (path : (before.seq checked).Path) (resident auxiliary : SpacePool model.kind)
    (beforeSpace : before.peakResidentSpace path.1 ≤ resident ∧
      before.peakAuxiliarySpace path.1 ≤ auxiliary)
    (checkedSpace : checked.peakResidentSpace path.2 ≤ resident ∧
      checked.peakAuxiliarySpace path.2 ≤ auxiliary) :
    (before.seq checked).peakResidentSpace path ≤ resident ∧
      (before.seq checked).peakAuxiliarySpace path ≤ auxiliary :=
  ⟨(Circuit.peakResidentSpace_seq before checked path).trans_le
      (SpacePool.max_le beforeSpace.1 checkedSpace.1),
    (Circuit.peakAuxiliarySpace_seq before checked path).trans_le
      (SpacePool.max_le beforeSpace.2 checkedSpace.2)⟩

private lemma resources_of_pool_and_space {model : ExecutionModel}
    {origin final : RuntimeCtx model.kind} (code : Circuit model origin final)
    (path : code.Path) (budget : ResourcePool model) (resident auxiliary : SpacePool model.kind)
    (events : code.resourcePool path ≤ budget)
    (space : code.peakResidentSpace path ≤ resident ∧ code.peakAuxiliarySpace path ≤ auxiliary) :
    code.resourcePool path ≤ budget ∧ code.peakResidentSpace path ≤ resident ∧
      code.peakAuxiliarySpace path ≤ auxiliary ∧
      code.quantumTime path ≤ ResourcePool.weightedCount (fun _ => 1) budget :=
  ⟨events, space.1, space.2,
    (Circuit.quantumTime_le_unitDepth code path).trans
      (Circuit.depth_le_weightedCount_of_pool_le code (fun _ => 1) budget path events)⟩

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

omit [Fact p.Prime] in
private lemma prefix_pool (path : («prefix» E problem).Path) :
    («prefix» E problem).resourcePool path =
      BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size) := by
  change ResourcePool.ofList
    ((BitWord.selectForCircuit
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).eventTrace path.1 ++
        (retainPersistent (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
          (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).eventTrace path.2) = _
  rw [ResourcePool.ofList_append]
  change _ + (retainPersistent (model := Model)
    (Recovery.PublicInput.context E (orderWidth problem))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).resourcePool path.2 = _
  rw [retainPersistent_resourcePool, add_zero]
  exact Events.selected_allocation_pool E (orderWidth problem) path.1

omit [Fact p.Prime] in
private lemma prefix_space (path : («prefix» E problem).Path) :
    («prefix» E problem).peakResidentSpace path = (sectionCtx E problem).residentSpace ∧
      («prefix» E problem).peakAuxiliarySpace path = (sectionCtx E problem).auxiliarySpace := by
  let allocated := BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E
    (orderWidth problem))
  let retained := retainPersistent (model := Model)
    (Recovery.PublicInput.context E (orderWidth problem))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
  change (allocated.seq retained).peakResidentSpace path = _ ∧
    (allocated.seq retained).peakAuxiliarySpace path = _
  have resident := BitWord.selectForCircuit_peakResidentSpace
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))
    ((BitWord.selectForCircuitPathEquiv
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).symm path.1)
  have auxiliary := BitWord.selectForCircuit_peakAuxiliarySpace
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))
    ((BitWord.selectForCircuitPathEquiv
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).symm path.1)
  simp only [Equiv.apply_symm_apply] at resident auxiliary
  constructor
  · rw [Circuit.peakResidentSpace_seq allocated retained path]
    change SpacePool.max (allocated.peakResidentSpace path.1)
      (retained.peakResidentSpace path.2) = _
    rw [resident, Recovery.PublicInput.Allocation.circuit_peakResidentSpace,
      retainPersistent_resident]
    apply SpacePool.max_eq_right
    exact (persistent_space_mono (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).1
  · rw [Circuit.peakAuxiliarySpace_seq allocated retained path]
    change SpacePool.max (allocated.peakAuxiliarySpace path.1)
      (retained.peakAuxiliarySpace path.2) = _
    rw [auxiliary, Recovery.PublicInput.Allocation.circuit_peakAuxiliarySpace,
      retainPersistent_auxiliary]
    apply SpacePool.max_eq_right
    exact (persistent_space_mono (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).2

/-- The same actual initialized path meets every original independent resource allowance. -/
lemma initialized_resources (nontrivial : 2 ≤ problem.order)
    (path : (initializedAlgorithm E fieldTail problem points seed r coefficient
      nontrivial).run.code.Path) :
    (initializedAlgorithm E fieldTail problem points seed r coefficient
      nontrivial).run.code.resourcePool path ≤ initializedBudget E problem nontrivial ∧
      (initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.peakResidentSpace path ≤
        (sectionResources E problem nontrivial).resident ∧
      (initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.peakAuxiliarySpace path ≤
        (sectionResources E problem nontrivial).auxiliary ∧
      (initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.quantumTime path ≤ ResourcePool.weightedCount (fun _ => 1)
          (initializedBudget E problem nontrivial) := by
  apply resources_of_pool_and_space
    (initializedAlgorithm E fieldTail problem points seed r coefficient nontrivial).run.code
    path (initializedBudget E problem nontrivial)
    (sectionResources E problem nontrivial).resident
    (sectionResources E problem nontrivial).auxiliary
  · exact sequence_pool_le («prefix» E problem)
      (first E fieldTail problem points seed r coefficient nontrivial) path
      (BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size))
      (sectionBudget E problem nontrivial) (prefix_pool E problem path.1).le
      (first_pool_le E fieldTail problem points seed r coefficient nontrivial path.2)
  · apply sequence_space_le («prefix» E problem)
      (first E fieldTail problem points seed r coefficient nontrivial) path
      (sectionResources E problem nontrivial).resident
      (sectionResources E problem nontrivial).auxiliary ?_
      ((section_space_certificate E fieldTail problem points seed r coefficient
        nontrivial).1 path.2)
    have beforeSpace := prefix_space E problem path.1
    exact ⟨beforeSpace.1.le.trans (fun _ => Nat.le_add_left _ _),
      beforeSpace.2.le.trans (fun _ => Nat.le_add_left _ _)⟩

/-- The complete first cycle restores every borrowed value jointly with arbitrary Reference. -/
lemma initialized_borrowed (nontrivial : 2 ≤ problem.order)
    {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    (initializedAlgorithm E fieldTail problem points seed r coefficient
      nontrivial).run.RestoresBorrowed environment input := by
  exact owned_input_restores
    (initializedAlgorithm E fieldTail problem points seed r coefficient nontrivial).run rfl input

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
