/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Space
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources

/-!
# Complete native events of the same allocated finite streaming recovery

Five initial physical zero preparations, each actual reset and converted
sampler, every original native checked attempt and one final paid option pack
are charged on the full Run3 Path. Count zero retains the initial allocation
and final pack. The original scalar gate ceilings already pay for reset X
corrections; every reset and sampler measurement is charged separately.

All allowances are independent parameter formulas. No actual code defines
its own budget, and no success, input support or caller budget premise is
introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Events

noncomputable section

open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open _root_.QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
  (sampledRecoveryEnvelope sampledRecoveryTail_pool_le sampledAttemptsEnvelope)

private abbrev QuantumModel : ExecutionModel := .quantum AlgorithmGate.model .empty
private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

/-- The original three gate ceilings, sampler Z writes, and every physical reset Z write. -/
def roundBudget (width m : Nat) : ResourcePool QuantumModel :=
  Recovery.Conversion.Events.gateBudget width m +
    Recovery.PublicInput.Allocation.Events.bankWidth width •
      ResourcePool.singleton (model := QuantumModel) (.measurement (2 : ℕ+))

/-- Rearrange the reset envelope before substituting a concrete sampler pool. -/
private lemma resetBudget_add (count : Nat) (sampler : ResourcePool QuantumModel) :
    count • Recovery.Initialization.Events.wireBudget + sampler =
      (count • ResourcePool.singleton (model := QuantumModel) (.gate .singleQubit) + sampler) +
        count • ResourcePool.singleton (model := QuantumModel) (.measurement (2 : ℕ+)) := by
  rw [Recovery.Initialization.Events.wireBudget, nsmul_add]
  ac_rfl

/-- Pure layout cardinality of the same terminal, including all zero-wire retained cells. -/
lemma terminal_systemCount (width m : Nat) :
    (Recovery.Layout.terminal width m).systemCount =
      Recovery.PublicInput.Allocation.Events.bankWidth width := by
  have systems : (Recovery.Layout.terminal width m).systemCount =
      (Recovery.Layout.terminal width m).residentSpace (.quantumSystems 2) := by
    rw [RuntimeCtx.residentSpace_quantumSystems]
    simp [QuantumLayout.dimensionCount, QuantumLayout.dimensions,
      Recovery.Initialization.newReset_qubits, List.ofFn_const]
  have counted := (Recovery.Layout.streamingTerminal_quantumSystems width m 2).1
  exact systems.trans (by
    simpa only [SpacePool.count, if_true, Recovery.PublicInput.Allocation.Events.bankWidth]
      using counted)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

attribute [local irreducible] Recovery.Initialization.newReset Recovery.Conversion.convertedStages

/-- Reset X corrections and the full converted sampler fit the original scalar gate envelope. -/
lemma samplingBody_budget
    (path : (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem)
      seed r points coefficient).Path) :
    (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem)
      seed r points coefficient).resourcePool path ≤ roundBudget p.size (orderWidth problem) := by
  have reset := Recovery.Initialization.Events.newReset_budget E fieldTail
    (orderWidth problem) seed path.1
  rw [terminal_systemCount] at reset
  have gates := Recovery.Conversion.Events.convertedStages_original_gateBudget E problem
    r points coefficient path.2
  change Recovery.PublicInput.Allocation.Events.bankWidth p.size •
      ResourcePool.singleton (model := QuantumModel) (.gate .singleQubit) +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).resourcePool path.2 ≤
      Recovery.Conversion.Events.gateBudget p.size (orderWidth problem) at gates
  change ResourcePool.ofList
    ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).eventTrace path.1 ++
      (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
        coefficient).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  calc
    _ ≤ Recovery.PublicInput.Allocation.Events.bankWidth p.size •
          Recovery.Initialization.Events.wireBudget +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).resourcePool path.2 := add_le_add reset le_rfl
    _ = (Recovery.PublicInput.Allocation.Events.bankWidth p.size •
          ResourcePool.singleton (model := QuantumModel) (.gate .singleQubit) +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).resourcePool path.2) +
        Recovery.PublicInput.Allocation.Events.bankWidth p.size •
          ResourcePool.singleton (model := QuantumModel) (.measurement (2 : ℕ+)) :=
        resetBudget_add _ _
    _ ≤ roundBudget p.size (orderWidth problem) := add_le_add gates le_rfl

private lemma selected_pool_le {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit QuantumModel pre post allowAllocation) (pool : ResourcePool QuantumModel)
    (bounded : ∀ path, code.resourcePool path ≤ pool)
    (path : (BitWord.selectForCircuit code).Path) :
    (BitWord.selectForCircuit code).resourcePool path ≤ BitWord.liftQuantumPool pool := by
  have selected := BitWord.selectForCircuit_resourcePool code
    ((BitWord.selectForCircuitPathEquiv code).symm path)
  simp only [Equiv.apply_symm_apply] at selected
  rw [selected]
  exact Multiset.map_le_map (bounded _)

/-- The exact native selection and actual public embedding keep every child event on its Path. -/
lemma round_budget
    (path : (round E fieldTail problem points seed r coefficient).Path) :
    (round E fieldTail problem points seed r coefficient).resourcePool path ≤
      BitWord.liftQuantumPool (roundBudget p.size (orderWidth problem)) := by
  change (BitWord.selectForCircuit (Circuit.embed (allowAllocation := false)
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem)
      seed r points coefficient))).resourcePool path ≤ _
  apply selected_pool_le
  intro originalPath
  rw [Circuit.resourcePool_embed]
  exact samplingBody_budget E fieldTail problem points seed r coefficient originalPath

omit [Fact p.Prime] in
/-- Native model selection preserves the complete physical initial preparation pool exactly. -/
lemma selected_allocation_pool (m : Nat)
    (path : (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E m)).Path) :
    (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E m)).resourcePool path =
      BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size) := by
  have selected := BitWord.selectForCircuit_resourcePool
    (Recovery.PublicInput.Allocation.circuit E m)
    ((BitWord.selectForCircuitPathEquiv (Recovery.PublicInput.Allocation.circuit E m)).symm path)
  simp only [Equiv.apply_symm_apply] at selected
  exact selected.trans (congrArg BitWord.liftQuantumPool
    (Recovery.PublicInput.Allocation.Events.circuit_pool E m _))

/-- Independent initial preparation, finite sample/check envelope, and one actual final pack. -/
def fullBudget (nontrivial : 2 ≤ problem.order) (count : Nat) : ResourcePool Model :=
  BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size) +
    sampledRecoveryEnvelope Model
      (BitWord.liftQuantumPool (roundBudget p.size (orderWidth problem)))
      (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial) count

/-- Every full actual Run3 Path pays the allocation, every complete native round, and final pack. -/
lemma run_budget (nontrivial : 2 ≤ problem.order) (count : Nat)
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.resourcePool path ≤
      fullBudget E problem nontrivial count := by
  have tail := sampledRecoveryTail_pool_le
    (round E fieldTail problem points seed r coefficient) count
    (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
    (recoveryInput (orderWidth problem)
      (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth
        problem))))
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))
    (BitWord.liftQuantumPool (roundBudget p.size (orderWidth problem)))
    (round_budget E fieldTail problem points seed r coefficient) path.2
  change ResourcePool.ofList
    ((BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth
      problem))).eventTrace
        path.1 ++
      (tailRun E fieldTail problem points seed r coefficient nontrivial count).code.eventTrace
        path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (selected_allocation_pool E (orderWidth problem) path.1).le tail

omit [Fact p.Prime] in
/-- With no attempts, the independent budget still contains all preparation and paid packing. -/
lemma fullBudget_zero (nontrivial : 2 ≤ problem.order) :
    fullBudget E problem nontrivial 0 =
      BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size) +
        ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := Model)
          (.nominalEncoding (.packOption (orderWidth problem))))] := by
  simp only [fullBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope, ResourcePool.scale,
    zero_nsmul, zero_add]

end

end ExecutionContract.Events
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
