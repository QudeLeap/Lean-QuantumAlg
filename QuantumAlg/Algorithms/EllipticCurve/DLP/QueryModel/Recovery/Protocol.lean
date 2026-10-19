/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Specification

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.State
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.State.Requirement

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing

/-!
# Independent full original-input finite declared-query ECDLP protocol
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] persistentCtx

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original bounded natural-scalar equation, with absent output rejected. -/
public def wholeAccepts (I : ECDLPInstance E)
    (output : (CShape.option (.unsignedWord (scalarWidth I))).Value) : Prop := by
  letI : Fact p.Prime := ⟨E.prime⟩
  exact match output with
  | .optionNone => False
  | .optionSome value => value.toNat < I.subgroupOrder ∧
      value.toNat • I.basePoint.toMathlib = I.targetPoint.toMathlib

/-- Every complete optional result fiber has the original full owned zero state. -/
public def wholeStateRequirement (I : ECDLPInstance E) :
    StateRequirement (Sampling.pre I) (post I) :=
  .marginal (post I).borrowedSelectionᶜ
    (.read (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))
    (fun _ _ => .pure (NormalizedVector.ket (wholeZeroSeed I)))

/-- The original public inputs request a finite checked ECDLP computation.

**Input.** Original affine public points, arbitrary references
and joint execution history. No secret, candidate or prepared bank is supplied.
**Output.** A bounded natural scalar multiplying the original base to the
original target, or the actual absent result. Every result fiber has the
prescribed full owned zero bank and restored borrowed observations.
**Resource budget.** One actual bank preparation, all real sampling/reset,
checked recovery and feedback rounds, one paid option pack, and both full
resident and auxiliary inventories. Whole-run quantum time is bounded by the quantum-weighted
  event allowance.
**Success.** The original finite geometric selected-family floor, including
zero rounds; the original public failure budget determines calibrated repeats.
**Source.** [PZ03, ecc.tex:448-462,525-640]; [Sho95, source.tex:1704-1740];
[SV24, Uniform.tex:622-664,775-805,996-1024]; [RNSL17, ECDLP.tex:483-510,649-709].
-/
public def wholeProblem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Problem (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) where
  Witness := FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I)
  valid := fun environment _ state => Sampling.Admissible I environment ∧ inputDomain I state
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ result => wholeAccepts I result
  successLB := fun _ _ => ⟨1 - ENNReal.ofReal ((1 - Sampling.Reuse.successFloor I) ^ count),
    tsub_le_self⟩
  states := fun _ _ => [wholeStateRequirement I]
  resources :=
    { events := eventBudget I expansion nontrivial count
      resident := tailResidentBudget I
      auxiliary := tailAuxiliaryBudget I }
  quantumTimeLimit := ResourcePool.weightedCount Resource.Event.quantumDuration
    (eventBudget I expansion nontrivial count)

/-- Execute the same original allocation, actual checked rounds and sole terminal pack. -/
public def wholeAlgorithm (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Algorithm (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) := ⟨run I expansion nontrivial count⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
