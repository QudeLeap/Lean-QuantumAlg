/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Distribution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Group
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model.Bounds

/-!
# Original selected samples satisfy the complete native candidate condition

The actual retained vector is read in its original big-endian order. The
pure decoder, checked inverse and reconstruction return the original secret
on every selected unit, with its full word capacity proved from the order.
The complete natural-scalar point equation identifies the same secret.
This proof introduces no secret or candidate promise into execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open FiniteCyclicDLP.Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

attribute [local implicit_reducible] problem

private lemma scalar_target_iff (I : ECDLPInstance E) (scalar : Nat) :
    scalar • I.basePoint.toMathlib = I.targetPoint.toMathlib ↔
      (problem I).generator ^ scalar = (problem I).target := by
  change scalar • (problem I).generator.toMathlib = (problem I).target.toMathlib ↔ _
  rw [← Canonical.Recovery.AttemptSoundness.groupPoint_pow_toMathlib
    E (problem I).generator scalar]
  constructor
  · intro equality
    exact (groupPointEquiv E).injective equality
  · intro equality
    exact congrArg GroupPoint.toMathlib equality

/-- The point equation uniquely determines the original canonical secret within its order. -/
lemma bounded_scalar_target_iff (I : ECDLPInstance E) (input : SecretInput (problem I))
    (scalar : Nat) (bounded : scalar < I.subgroupOrder) :
    scalar • I.basePoint.toMathlib = I.targetPoint.toMathlib ↔ scalar = input.secret.val := by
  rw [scalar_target_iff]
  constructor
  · intro accepted
    have sameResidue := pow_inj_mod.mp (accepted.trans input.target_eq_generator_pow.symm)
    have secretBound : input.secret.val < (problem I).order :=
      (residueIndex (problem I) input.secret).isLt
    have actualBound : scalar < (problem I).order := bounded
    rw [← (problem I).order_eq_orderOf, Nat.mod_eq_of_lt actualBound,
      Nat.mod_eq_of_lt secretBound] at sameResidue
    exact sameResidue
  · intro same
    rw [same]
    exact input.target_eq_generator_pow

/-- The original selected raw outcome passes the actual flags and full public point equation. -/
lemma selectedOutcome_accepted (I : ECDLPInstance E) (nontrivial : 2 ≤ (problem I).order)
    (input : SecretInput (problem I)) (unit : (ZMod (problem I).order)ˣ)
    (sample : CShape.Value (.fixedVector (scalarWidth I + scalarWidth I) (.finite 2)))
    (selected : Sampling.observedOutcome I sample = selectedRawOutcome (problem I) input unit) :
    SampleAccepted (curve E) (modulus I nontrivial)
      I.basePoint.toMathlib I.targetPoint.toMathlib sample := by
  have raw : ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput sample =
      RecoveryBridge.selectedRawInput (problem I) input unit := by
    change CShape.Value.bits (Sampling.observedOutcome I sample) = _
    rw [selected]
    rfl
  obtain ⟨output, recovered, candidate, verified⟩ :=
    RecoveryBridge.outputOf_selectedRawInput_recovers (problem I) input unit
      (modulus I nontrivial) rfl
  have secretFits : input.secret.val < 2 ^ scalarWidth I :=
    lt_of_lt_of_le (residueIndex (problem I) input.secret).isLt
      (FiniteCyclicDLP.order_le_fourierModulus (problem I))
  unfold SampleAccepted
  rw [raw, ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    (modulus I nontrivial) _ output recovered, candidate, verified]
  change (input.secret.val % 2 ^ scalarWidth I) • I.basePoint.toMathlib =
    I.targetPoint.toMathlib ∧ true = true ∧ true = true
  rw [Nat.mod_eq_of_lt secretFits]
  exact ⟨(scalar_target_iff I input.secret.val).mpr input.target_eq_generator_pow, rfl, rfl⟩

/-- Every accepted raw sample has exactly the canonical original secret and both true flags. -/
lemma sampleAccepted_iff_secret (I : ECDLPInstance E)
    (nontrivial : 2 ≤ (problem I).order) (input : SecretInput (problem I))
    (sample : CShape.Value (.fixedVector (scalarWidth I + scalarWidth I) (.finite 2))) :
    SampleAccepted (curve E) (modulus I nontrivial)
      I.basePoint.toMathlib I.targetPoint.toMathlib sample ↔
      let raw := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells (modulus I nontrivial)
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput sample)
      raw.second.first.toNat = input.secret.val ∧
        raw.first.toBool = true ∧ raw.second.second.toBool = true := by
  dsimp only [SampleAccepted]
  exact and_congr (bounded_scalar_target_iff I input _
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_candidate_lt
      (modulus I nontrivial) _)) Iff.rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
