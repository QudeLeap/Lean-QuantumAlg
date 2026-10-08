/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.SuccessFloor
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Admission
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent complete-round ECDLP protocol

The result observes the existing accepted bit and selected word without a new
packing instruction. The complete computation includes checked recovery and
feedback before its fixed physical restart. Its domain, original point
relation, source floor and native resource allowances name no candidate code.
Quantum input and scratch remain arbitrary; every reference extension and
joint service correlation of an admitted local input is retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Read the same live first-success latch and word without allocating or packing a new value. -/
public def roundResultRead (I : ECDLPInstance E) :
    OutputRead (context I) (.product .bit (.unsignedWord (scalarWidth I))) :=
  .read (.product
    (.storage (persistentAccepted (Sampling.Reuse.context I)
      (fieldWidth E) (scalarWidth I)).toCStorageRef)
    (.storage (persistentSelected (Sampling.Reuse.context I)
      (fieldWidth E) (scalarWidth I)).toCStorageRef))

/-- Acceptance is the original bounded natural-scalar equation in the actual live result. -/
public def roundAccepts (I : ECDLPInstance E)
    (result : (CShape.product .bit (.unsignedWord (scalarWidth I))).Value) : Prop := by
  letI : Fact p.Prime := ⟨E.prime⟩
  exact result.first.toBool = true ∧ result.second.toNat < I.subgroupOrder ∧
    result.second.toNat • I.basePoint.toMathlib = I.targetPoint.toMathlib

/-- Every result fiber has the same independently specified physical zero seed. -/
public def roundStateRequirement (I : ECDLPInstance E) :
    StateRequirement (context I) (context I) :=
  .marginal (context I).borrowedSelectionᶜ (roundResultRead I)
    (fun _ _ => .pure (NormalizedVector.ket (roundZeroSeed I)))

/-- Local joint seed property retaining arbitrary reference extensions and all record masses. -/
public def roundSeededDomain (I : ECDLPInstance E) (A : Access I)
    (state : ExecutionState (Store (context I) × (Sampling.executionModel I A).HiddenState)
      (context I).register) : Prop :=
  Circuit.JointSeededInitialization (model := Sampling.executionModel I A)
    (context I) (roundZeroSeed I) state

/-- The complete checking scratch and all seven retained cells coexist with the original bank. -/
public def roundResidentBudget (I : ECDLPInstance E) : SpacePool .quantum :=
  attemptScratchSpace .quantum (fieldWidth E) (scalarWidth I) + (context I).residentSpace

/-- The same native scratch allowance preserves every existing auxiliary role. -/
public def roundAuxiliaryBudget (I : ECDLPInstance E) : SpacePool .quantum :=
  attemptScratchSpace .quantum (fieldWidth E) (scalarWidth I) + (context I).auxiliarySpace

/-- One complete quantum ECDLP attempt with paid checking, feedback and physical restart.

**Input.**
- Original affine public points and a bounded sound persistent
  selection, with arbitrary quantum input, scratch, joint service and reference state.
**Output.**
- The actual retained accepted bit and selected word, every live entry,
  restored borrowed correlations and the same fixed zero owned bank on every result.
**Resource budget.**
- Two full bank resets, one declared group query, actual order preparation,
  inverse Fourier transforms, exponent measurements and complete native checking.
- Checking scratch and all live storage are bounded separately by dimension;
  serial depth is bounded by the independently specified full event allowance.
**Success.**
- The original selected-family floor; every accepted word is below the original
  subgroup order and multiplies the original base to the original target.
**Source.**
- [PZ03, ecc.tex:448-462,525-640]; [Sho95, source.tex:1704-1740].
- [SV24, Uniform.tex:622-664,775-805,996-1024] for known-order preparation.
- [RNSL17, ECDLP.tex:483-510,649-709] for native checked curve arithmetic.
-/
public def roundProblem (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem (Sampling.executionModel I A) (context I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) where
  valid := fun _ => True
  initialization := roundInputDomain I A
  accepts := fun _ result => roundAccepts I result
  successLB := ⟨ENNReal.ofReal (Sampling.Reuse.successFloor I),
    ENNReal.ofReal_le_one.mpr (successFloor_le_one I)⟩
  states := [roundStateRequirement I]
  resources :=
    { events := roundEventBudget I A expansion nontrivial
      resident := roundResidentBudget I
      auxiliary := roundAuxiliaryBudget I }
  depth :=
    { duration := duration
      limit := ResourcePool.weightedCount duration (roundEventBudget I A expansion nontrivial)
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := unitQueries }

/-- The sole actual complete round exposes all live entries with its two existing result cells. -/
public def roundAlgorithm (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Algorithm (Sampling.executionModel I A) (context I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) where
  run := ⟨round I A expansion nontrivial, Output.all (context I) (roundResultRead I)⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
