/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources.Bounds

/-!
# Numerical coordinates of the actual fresh-feedback recovery factory

The native ledger belongs to the same real three-attempt program. The 769
feedback bits are charged while live, the seven retained checker cells add
1037 bits once, and every original caller entry remains in the bound. This
resource certificate supplies no Born or success-probability statement.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution ClassicalRoutines

namespace Storage.Inputs

private lemma scoped_extra_le {kind : ProblemKind}
    (feedback sample checker output : SpacePool kind) :
    SpacePool.max (feedback + SpacePool.max sample checker) output ≤
      feedback + SpacePool.max (SpacePool.max sample checker) output := by
  refine SpacePool.max_le (add_le_add le_rfl (SpacePool.le_max_left _ _)) ?_
  exact (SpacePool.le_max_right _ _).trans (le_add_of_nonneg_left zero_le)

private lemma runAdditional_le :
    runAdditionalSpace ≤ frameSpace .quantum 256 256 +
      Recovery.Parameters.runAdditionalSpace :=
  scoped_extra_le _ _ _ _

private lemma classical_coordinates_bound (actual feedback original : SpacePool .quantum)
    (combined : actual ≤ feedback + original) (feedbackBound : feedback .classicalBits ≤ 769)
    (originalBound : original .classicalBits ≤ 85079359) :
    actual .classicalBits ≤ 85080128 := by
  have bound : actual .classicalBits ≤
      feedback .classicalBits + original .classicalBits := combined .classicalBits
  omega

attribute [local irreducible] runAdditionalSpace attemptAdditionalSpace frameSpace
  Recovery.Parameters.runAdditionalSpace
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace

/-- The original five-array/checker ceiling coexists with all 769 actual feedback bits. -/
lemma runAdditional_classical_le : runAdditionalSpace .classicalBits ≤ 85080128 := by
  exact classical_coordinates_bound runAdditionalSpace (frameSpace .quantum 256 256)
    Recovery.Parameters.runAdditionalSpace runAdditional_le
    (frameSpace_classicalBits .quantum 256 256).le
    Recovery.Parameters.runAdditional_classical_le

/-- The lexical feedback and all later scratch allocate only classical cells. -/
lemma runAdditional_quantumSystems (dimension : ℕ+) :
    runAdditionalSpace (.quantumSystems dimension) = 0 := by
  have actual := runAdditional_le (.quantumSystems dimension)
  rw [Pi.add_apply, frameSpace_quantumSystems,
    Recovery.Parameters.runAdditional_quantumSystems, Nat.zero_add] at actual
  exact Nat.eq_zero_of_le_zero actual

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)

attribute [local irreducible] run Circuit.resourcePool

/-- The actual 102 point drivers retain the same independently proved Toffoli allowance. -/
lemma run_toffoli_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      .toffoli)
      ((original.run (services := services)).code.resourcePool path) ≤ 99272733288 :=
  original.run_native_count_le (services := services) .toffoli path

/-- All actual CNOT work remains charged on the same complete factory path. -/
lemma run_cnot_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      .cnot)
      ((original.run (services := services)).code.resourcePool path) ≤ 81134896044 :=
  original.run_native_count_le (services := services) .cnot path

/-- Single-qubit work includes all real loader, Fourier and reset corrections. -/
lemma run_singleQubit_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      .singleQubit)
      ((original.run (services := services)).code.resourcePool path) ≤ 25700866770 :=
  original.run_native_count_le (services := services) .singleQubit path

/-- The resident ceiling includes fresh feedback, retained checkers and all caller bits. -/
lemma run_resident_classical_le (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakResidentSpace path .classicalBits ≤
      85081165 + ctx.residentSpace .classicalBits := by
  have actual := original.run_resident_le (services := services) path .classicalBits
  have extra := runAdditional_classical_le
  rw [EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits] at actual
  change _ ≤ runAdditionalSpace .classicalBits + 1037 +
    ctx.residentSpace .classicalBits at actual
  omega

/-- The auxiliary ceiling keeps all original classical roles under the same lexical maximum. -/
lemma run_auxiliary_classical_le (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakAuxiliarySpace path .classicalBits ≤
      85081165 + ctx.auxiliarySpace .classicalBits := by
  have actual := original.run_auxiliary_le (services := services) path .classicalBits
  have extra := runAdditional_classical_le
  rw [EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits] at actual
  change _ ≤ runAdditionalSpace .classicalBits + 1037 +
    ctx.auxiliarySpace .classicalBits at actual
  omega

/-- Every original resident quantum system remains, with no new quantum system in any dimension. -/
lemma run_resident_quantumSystems (dimension : ℕ+)
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakResidentSpace path (.quantumSystems dimension) =
      ctx.residentSpace (.quantumSystems dimension) := by
  apply le_antisymm
  · have actual := original.run_resident_le (services := services) path
      (.quantumSystems dimension)
    simpa only [Pi.add_apply, runAdditional_quantumSystems,
      EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits, SpacePool.ofShape,
      Nat.zero_add] using actual
  · have input := (original.run (services := services)).code.input_residentSpace_le_peak path
    exact input (.quantumSystems dimension)

/-- Actual auxiliary quantum roles are preserved exactly beside the classical feedback scope. -/
lemma run_auxiliary_quantumSystems (dimension : ℕ+)
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakAuxiliarySpace path (.quantumSystems dimension) =
      ctx.auxiliarySpace (.quantumSystems dimension) := by
  apply le_antisymm
  · have actual := original.run_auxiliary_le (services := services) path
      (.quantumSystems dimension)
    simpa only [Pi.add_apply, runAdditional_quantumSystems,
      EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits, SpacePool.ofShape,
      Nat.zero_add] using actual
  · have input := (original.run (services := services)).code.input_auxiliarySpace_le_peak path
    exact input (.quantumSystems dimension)

end Storage.Inputs

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
