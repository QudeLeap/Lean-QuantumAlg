/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Space.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Space
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources.Numeric

/-!
# Space of the complete paid P-256 factory

The signed preparation and finalized sampler reuse scratch capacity. Every
bound includes the real retained banks and preserves the original caller's
resident or auxiliary pool explicitly.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

attribute [local irreducible] RuntimeCtx.residentSpace RuntimeCtx.auxiliarySpace
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace
  Sampling.Storage.Inputs.runAdditionalSpace

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private lemma prefix_scratch_le :
    (SpacePool.ofShape (.bits 1194561) : SpacePool .quantum) ≤
      SpacePool.ofShape (.bits 85081165) := by
  intro axis
  cases axis <;> norm_num [SpacePool.ofShape, CShape.bitWidth]

private lemma finalized_classical_le (extra : Nat) (bound : extra ≤ 85080128) :
    extra + 1037 ≤ 85081165 := by
  calc
    extra + 1037 ≤ 85080128 + 1037 := Nat.add_le_add_right bound 1037
    _ = 85081165 := by decide

private lemma finalized_pool_le (extra : SpacePool .quantum)
    (classical : extra .classicalBits ≤ 85080128)
    (quantum : ∀ dimension, extra (.quantumSystems dimension) = 0) :
    extra + SpacePool.ofShape (.bits 1037) ≤ SpacePool.ofShape (.bits 85081165) := by
  intro axis
  cases axis with
  | classicalBits =>
      exact finalized_classical_le _ classical
  | quantumSystems dimension =>
      simpa only [Pi.add_apply, SpacePool.ofShape, Nat.add_zero] using (quantum dimension).le

private lemma finalized_additional_le :
    Sampling.Storage.Inputs.runAdditionalSpace +
      CandidateCheck.Native.persistentCellSpace .quantum 256 260 ≤
        SpacePool.ofShape (.bits 85081165) := by
  simpa only [CandidateCheck.Native.persistentCellSpace_eq_bits] using
    finalized_pool_le Sampling.Storage.Inputs.runAdditionalSpace
      Sampling.Storage.Inputs.runAdditional_classical_le
      Sampling.Storage.Inputs.runAdditional_quantumSystems

variable (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- The whole actual run reuses one sequential scratch ceiling over its live allocated context. -/
lemma paidRun_resident_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakResidentSpace
      path ≤ SpacePool.ofShape (.bits 85081165) + (tableContext base noQuantum).residentSpace := by
  have initialization := ((paidPrefix_space base noQuantum I basePoint targetPoint path.1).1).trans
    (add_le_add prefix_scratch_le le_rfl)
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_resident_le
      (services := services) path.2
  unfold paidRun at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le initialization
    (continuation.trans (add_le_add finalized_additional_le le_rfl))

/-- The actual auxiliary peak uses the same scopes and preserves all original caller roles. -/
lemma paidRun_auxiliary_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakAuxiliarySpace
      path ≤ SpacePool.ofShape (.bits 85081165) + (tableContext base noQuantum).auxiliarySpace := by
  have initialization := ((paidPrefix_space base noQuantum I basePoint targetPoint path.1).2).trans
    (add_le_add prefix_scratch_le le_rfl)
  have continuation :=
    (retainedInputs base noQuantum I basePoint targetPoint).runFinalized_auxiliary_le
      (services := services) path.2
  unfold paidRun at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le initialization
    (continuation.trans (add_le_add finalized_additional_le le_rfl))

/-- All real allocated bits and the original caller's resident cells remain charged. -/
lemma paidRun_resident_classical_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakResidentSpace
      path .classicalBits ≤ 85101142 + base.residentSpace .classicalBits := by
  have actual := paidRun_resident_le base noQuantum I basePoint targetPoint path .classicalBits
  rw [Pi.add_apply, tableContext_resident_classicalBits] at actual
  simpa only [SpacePool.ofShape, CShape.bitWidth, ← Nat.add_assoc] using actual

/-- Auxiliary accounting retains the original caller role, without borrowing resident bits. -/
lemma paidRun_auxiliary_classical_le
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakAuxiliarySpace
      path .classicalBits ≤ 85101142 + base.auxiliarySpace .classicalBits := by
  have actual := paidRun_auxiliary_le base noQuantum I basePoint targetPoint path .classicalBits
  rw [Pi.add_apply, tableContext_auxiliary_classicalBits] at actual
  simpa only [SpacePool.ofShape, CShape.bitWidth, ← Nat.add_assoc] using actual

/-- Only the actual 854-system qubit bank is added in any quantum dimension. -/
lemma paidRun_resident_quantumSystems_le (dimension : ℕ+)
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakResidentSpace
      path (.quantumSystems dimension) ≤ (if (2 : ℕ+) = dimension then 854 else 0) +
        base.residentSpace (.quantumSystems dimension) := by
  have actual := paidRun_resident_le base noQuantum I basePoint targetPoint path
    (.quantumSystems dimension)
  rw [Pi.add_apply, tableContext_resident_quantumSystems] at actual
  simpa only [SpacePool.ofShape, Nat.zero_add] using actual

/-- Every owned bank system remains charged in the auxiliary coordinate as well. -/
lemma paidRun_auxiliary_quantumSystems_le (dimension : ℕ+)
    (path : (paidRun (services := services) base noQuantum I basePoint targetPoint).code.Path) :
    (paidRun (services := services) base noQuantum I basePoint targetPoint).code.peakAuxiliarySpace
      path (.quantumSystems dimension) ≤ (if (2 : ℕ+) = dimension then 854 else 0) +
        base.auxiliarySpace (.quantumSystems dimension) := by
  have actual := paidRun_auxiliary_le base noQuantum I basePoint targetPoint path
    (.quantumSystems dimension)
  rw [Pi.add_apply, tableContext_auxiliary_quantumSystems] at actual
  simpa only [SpacePool.ofShape, Nat.zero_add] using actual

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
