/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources

/-!
# Actual interleaved declared ECDLP tail resources

Every prescribed round charges both physical bank resets, its original query
word and every native checked-recovery instruction. Seven persistent recovery
destinations coexist with the original point inputs, complete quantum bank,
measured exponent cells and dedicated reset cell. Lexical checking scratch is
reused, so neither resident nor auxiliary peak grows with the round count.
The one actual terminal optional packing instruction is charged even at zero
rounds. The initial allocation prefix is accounted for separately.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- All real sampling/checking rounds and one actual final optional-result pack. -/
public def tailEventBudget (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    ResourcePool (Sampling.executionModel I A) :=
  sampledRecoveryEnvelope (Sampling.executionModel I A)
    (Sampling.Reuse.eventBudget I A expansion) (curve E) (modulus I nontrivial) count

/-- Every actual resident dimension, including borrowed inputs and reused checking scratch. -/
public def tailResidentBudget (I : ECDLPInstance E) : SpacePool .quantum :=
  recoveryTailScratchSpace .quantum (fieldWidth E) (scalarWidth I) +
    persistentCellSpace .quantum (fieldWidth E) (scalarWidth I) +
      (Sampling.Reuse.context I).residentSpace

/-- The same complete actual auxiliary inventory, respecting each original storage role. -/
public def tailAuxiliaryBudget (I : ECDLPInstance E) : SpacePool .quantum :=
  recoveryTailScratchSpace .quantum (fieldWidth E) (scalarWidth I) +
    persistentCellSpace .quantum (fieldWidth E) (scalarWidth I) +
      (Sampling.Reuse.context I).auxiliarySpace

/-- Every actual finite tail path charges native sampling, checking and final packing. -/
public theorem ecdlpRecovery_tail_events_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (tail I A expansion nontrivial count).Path) :
    (tail I A expansion nontrivial count).resourcePool path ≤
      tailEventBudget I A expansion nontrivial count :=
  sampledRecoveryTail_pool_le (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    (Sampling.Reuse.eventBudget I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_events_le I A expansion) path

/-- The full resident peak is bounded independently of the real prescribed round count. -/
public theorem ecdlpRecovery_tail_resident_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (tail I A expansion nontrivial count).Path) :
    (tail I A expansion nontrivial count).peakResidentSpace path ≤ tailResidentBudget I :=
  sampledRecoveryTail_resident_le (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path

/-- The auxiliary peak counts the same reused real storage roles for every round count. -/
public theorem ecdlpRecovery_tail_auxiliary_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (tail I A expansion nontrivial count).Path) :
    (tail I A expansion nontrivial count).peakAuxiliarySpace path ≤ tailAuxiliaryBudget I :=
  sampledRecoveryTail_auxiliary_le (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
