/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Compatibility
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.NativePool
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Space

/-!
# Actual complete first-cycle resource bounds

One-time native initialization is charged inside the first complete cycle.
The persistent allocation emits no operation event and reaches the one real
seven-cell bank. Its live space and the subsequent checked scratch are bounded
by the same independent reuse envelope, without counting repeated copies.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ScalarMultiplication.MeasuredPlacement
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

omit [Fact p.Prime] in
private theorem checkedRunPrefix_pool
    (path : (checkedRunPrefix E problem).Path) :
    (checkedRunPrefix E problem).resourcePool path = BitWord.liftQuantumPool
      (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))) := by
  let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
  let allocation := retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
  change setup.Path × allocation.Path at path
  change setup.resourcePool path.1 + allocation.resourcePool path.2 = _
  rw [retainPersistent_resourcePool, add_zero]
  exact selectedInitial_pool_eq E problem path.1

private theorem allocationAfterSetup_resident {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    (width scalarWidth : Nat) (scratch : SpacePool model.kind)
    (setupBound : ∀ path, setup.peakResidentSpace path ≤ ctx.residentSpace)
    (path : (setup.seq (retainPersistent ctx width scalarWidth)).Path) :
    (setup.seq (retainPersistent ctx width scalarWidth)).peakResidentSpace path ≤
      scratch + persistentCellSpace model.kind width scalarWidth + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (setupBound path.1).trans (fun _ => Nat.le_add_left _ _)
  · have allocation := (retainPersistent_resident ctx width scalarWidth path.2).trans
      (persistentCtx_residentSpace ctx width scalarWidth)
    exact allocation.le.trans (by
      rw [add_assoc]
      exact fun _ => Nat.le_add_left _ _)

private theorem allocationAfterSetup_auxiliary {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    (width scalarWidth : Nat) (scratch : SpacePool model.kind)
    (setupBound : ∀ path, setup.peakAuxiliarySpace path ≤ ctx.auxiliarySpace)
    (path : (setup.seq (retainPersistent ctx width scalarWidth)).Path) :
    (setup.seq (retainPersistent ctx width scalarWidth)).peakAuxiliarySpace path ≤
      scratch + persistentCellSpace model.kind width scalarWidth + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (setupBound path.1).trans (fun _ => Nat.le_add_left _ _)
  · have allocation := (retainPersistent_auxiliary ctx width scalarWidth path.2).trans
      (persistentCtx_auxiliarySpace ctx width scalarWidth)
    exact allocation.le.trans (by
      rw [add_assoc]
      exact fun _ => Nat.le_add_left _ _)

omit [Fact p.Prime] in
private theorem checkedRunPrefix_resident
    (path : (checkedRunPrefix E problem).Path) :
    (checkedRunPrefix E problem).peakResidentSpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).resident := by
  exact allocationAfterSetup_resident
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
    (recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem))
    (fun path => (selectedInitial_resident E problem path).le) path

omit [Fact p.Prime] in
private theorem checkedRunPrefix_auxiliary
    (path : (checkedRunPrefix E problem).Path) :
    (checkedRunPrefix E problem).peakAuxiliarySpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).auxiliary := by
  exact allocationAfterSetup_auxiliary
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
    (recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem))
    (fun path => (selectedInitial_auxiliary E problem path).le) path

private theorem prefixedCode_pool_le {model : ExecutionModel}
    {origin middle post : RuntimeCtx model.kind}
    (entryCode : Circuit model origin middle) (checkedCode : Circuit model middle post)
    (entryBudget checkedBudget : ResourcePool model)
    (entryBound : ∀ path, entryCode.resourcePool path ≤ entryBudget)
    (checkedBound : ∀ path, checkedCode.resourcePool path ≤ checkedBudget)
    (path : (entryCode.seq checkedCode).Path) :
    (entryCode.seq checkedCode).resourcePool path ≤ entryBudget + checkedBudget := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (entryBound path.1) (checkedBound path.2)

/-- Every actual complete first-cycle path charges initialization and the
entire checked section, including its following physical reset. -/
theorem initializedFirstCheckedSection_pool_le
    (path : (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).Path) :
    (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
      seed nontrivial).resourcePool path ≤
        initializedFirstCheckedSectionEventBudget E problem nontrivial := by
  exact prefixedCode_pool_le (checkedRunPrefix E problem)
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
    (BitWord.liftQuantumPool
      (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))))
    (checkedSectionEventBudget E problem nontrivial)
    (fun path => (checkedRunPrefix_pool E problem path).le)
    (firstCheckedSection_pool_le E fieldTail sameWidth fits odd problem points seed nontrivial)
    path

/-- The first complete cycle's peak includes one bank and successive scratch. -/
theorem initializedFirstCheckedSection_resident_le
    (path : (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).Path) :
    (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
      seed nontrivial).peakResidentSpace path ≤
        (checkedSectionResourceBudget E problem nontrivial).resident := by
  let entryCode := checkedRunPrefix E problem
  let checkedCode := firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
    nontrivial
  change entryCode.Path × checkedCode.Path at path
  exact (Circuit.peakResidentSpace_seq entryCode checkedCode path).le.trans
    (SpacePool.max_le (checkedRunPrefix_resident E problem nontrivial path.1)
      (firstCheckedSection_resident_le E fieldTail sameWidth fits odd problem points seed
        nontrivial path.2))

/-- The complete first cycle also counts every auxiliary role only once. -/
theorem initializedFirstCheckedSection_auxiliary_le
    (path : (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).Path) :
    (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
      seed nontrivial).peakAuxiliarySpace path ≤
        (checkedSectionResourceBudget E problem nontrivial).auxiliary := by
  let entryCode := checkedRunPrefix E problem
  let checkedCode := firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
    nontrivial
  change entryCode.Path × checkedCode.Path at path
  exact (Circuit.peakAuxiliarySpace_seq entryCode checkedCode path).le.trans
    (SpacePool.max_le (checkedRunPrefix_auxiliary E problem nontrivial path.1)
      (firstCheckedSection_auxiliary_le E fieldTail sameWidth fits odd problem points seed
        nontrivial path.2))

/-- The first complete cycle's chronological depth retains every charged
initialization, sampling, checking and reset dependency. -/
theorem initializedFirstCheckedSection_depth_le
    (path : (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).Path) :
    (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
      seed nontrivial).depth (fun _ => 1) path ≤
        ResourcePool.weightedCount (fun _ => 1)
          (initializedFirstCheckedSectionEventBudget E problem nontrivial) := by
  exact Circuit.depth_le_weightedCount_of_pool_le _ _ _ path
    (initializedFirstCheckedSection_pool_le E fieldTail sameWidth fits odd problem points
      seed nontrivial path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
