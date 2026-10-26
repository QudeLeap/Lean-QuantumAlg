/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Resources.Bounds
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Workspace
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-!
# Numeric classical work and storage of the same actual recovery run

The existing nearest checker and widened XGCD bounds are instantiated without
changing their execution widths. Every supplied caller cell remains charged.
The seven persistent checker cells contribute 1037 bits; feedback storage
supplied through the original input context remains in that context's pool.
An enclosing feedback allocator requires its own actual lexical-scope bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution ClassicalRoutines
open NumberTheory.XGCD.Native NumberTheory.Checked.SignedReduction
open NumberTheory.Checked.SignedReduction.Native Modular.Reduce.Native

namespace Recovery.Parameters

attribute [local irreducible]
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace

private lemma nearestAttempt_card_increase (model : ExecutionModel) [BitWord.Selected model]
    {width scalarWidth : Nat} (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth) :
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope model curve modulus).card =
      (EllipticCurve.CandidateCheck.Native.attemptEnvelope model curve modulus).card + 8 := by
  simp only [EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope,
    EllipticCurve.CandidateCheck.Native.attemptEnvelope,
    FiniteCyclicDLP.RawRecovery.Nearest.singleExposureEnvelope,
    FiniteCyclicDLP.RawRecovery.Native.singleExposureEnvelope,
    FiniteCyclicDLP.RawRecovery.Nearest.preparationEnvelope,
    FiniteCyclicDLP.RawRecovery.Native.preparationEnvelope,
    Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    FiniteCyclicDLP.RawRecovery.Nearest.scaleBodyEvents,
    FiniteCyclicDLP.RawRecovery.Native.scaleBodyEvents, List.length_cons, List.length_nil]
  omega

/-- The original paid nearest allowance has the same ceiling for arbitrary actual ports. -/
lemma nearestChecker_card_le (model : ExecutionModel) [BitWord.Selected model]
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec 260) :
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope model curve modulus).card ≤
      16685367 := by
  rw [nearestAttempt_card_increase]
  have old := EllipticCurve.CandidateCheck.Native.attemptEnvelope_card_le model curve modulus
  omega

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Recovery.Parameters ctx)

/-- The same actual nearest decoder retains its separately derived event ceiling. -/
lemma checker_card_le :
    (original.checkerBudget (services := services)).card ≤ 16685367 :=
  nearestChecker_card_le
    (.quantum AlgorithmGate.model .empty BitWord.model services) original.curve original.order

private lemma classical_event_weight_le_one {model : ExecutionModel}
    (event : Resource.Event model) : Resource.Event.classicalOperationWeight event ≤ 1 := by
  cases event with
  | classicalOperation => exact le_rfl
  | classicalQuery => exact Nat.zero_le 1
  | gate => exact Nat.zero_le 1
  | oracle => exact Nat.zero_le 1
  | preparation => exact Nat.zero_le 1
  | measurement => exact Nat.zero_le 1

private lemma classical_weight_le_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bounded : ∀ value ∈ pool.map Resource.Event.classicalOperationWeight, value ≤ 1 := by
    intro value present
    obtain ⟨event, _, rfl⟩ := Multiset.mem_map.mp present
    exact classical_event_weight_le_one event
  have actual := Multiset.sum_le_card_nsmul
    (pool.map Resource.Event.classicalOperationWeight) (1 : Nat) bounded
  simpa only [ResourcePool.weightedCount, Multiset.card_map, Nat.nsmul_eq_mul, Nat.mul_one]
    using actual

attribute [local irreducible] run checkerBudget ResourcePool.weightedCount Circuit.resourcePool

/-- Native classical work remains independent of every quantum event coordinate. -/
lemma run_classical_numeric_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.run (services := services)).code.resourcePool path) ≤ 20288182564 := by
  have actual := original.run_classical_le (services := services) path
  have weight := (classical_weight_le_card (original.checkerBudget (services := services))).trans
    (original.checker_card_le (services := services))
  refine actual.trans ?_
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 weight) (3 * samplerClassicalLimit)) 1

private lemma signedWidth_bound (width : Nat) :
    signedWidth width ≤ (width + 1) * (2 * (width + 1) + 1) + 3 := by
  simpa only [signedWidth, xgcdWidth, NumberTheory.XGCD.PureXGCD.executionCoefficientWidth]
    using ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_le_quadratic (width + 1)

private lemma sampleSignedWidth_le : signedWidth 260 ≤ 136506 :=
  signedWidth_bound 260

private lemma fieldSignedWidth_le : signedWidth 256 ≤ 132358 :=
  signedWidth_bound 256

attribute [local irreducible] signedWidth
  EllipticCurve.WindowTables.Outer.tableSpace
  EllipticCurve.WindowTables.Outer.coefficientScratchSpace

private lemma tableScratch_classical_bound (kind : ProblemKind)
    (width length ceiling : Nat)
    (scratch : EllipticCurve.WindowTables.Outer.coefficientScratchSpace kind width
      .classicalBits ≤ ceiling) :
    EllipticCurve.WindowTables.Outer.tableSpace kind width length .classicalBits +
      EllipticCurve.WindowTables.Outer.coefficientScratchSpace kind width .classicalBits ≤
      5 * length * width + ceiling := by
  rw [EllipticCurve.WindowTables.Outer.tableSpace_classicalBits]
  exact Nat.add_le_add_left scratch _

private lemma samplerAdditional_evaluation (axis : SpaceAxis .quantum) :
    samplerAdditionalSpace axis =
      EllipticCurve.WindowTables.Outer.tableSpace .quantum 256 (2 ^ 16) axis +
        EllipticCurve.WindowTables.Outer.coefficientScratchSpace .quantum 256 axis := rfl

attribute [local irreducible] samplerAdditionalSpace

/-- The five actual full arrays coexist with the original coefficient construction scratch. -/
lemma samplerAdditional_classical_le :
    samplerAdditionalSpace .classicalBits ≤ 85079359 := by
  have actual := tableScratch_classical_bound .quantum 256 (2 ^ 16) 1193279
    (EllipticCurve.WindowTables.Outer.coefficientScratchSpace256_classicalBits_le .quantum)
  exact (samplerAdditional_evaluation .classicalBits).le.trans actual

private lemma runAdditional_canonical :
    runAdditionalSpace = SpacePool.max samplerAdditionalSpace
      (EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace .quantum 256 260) :=
  SpacePool.max_assoc _ _ _

attribute [local irreducible] runAdditionalSpace

private lemma nearestScratch_classical_evaluation (kind : ProblemKind)
    (fieldWidth sampleWidth : Nat) :
    EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace
      kind fieldWidth sampleWidth .classicalBits =
      max (27 * sampleWidth + 9 * signedWidth sampleWidth + 17)
        (27 * fieldWidth + 9 * signedWidth fieldWidth + 15) :=
  congrArg (fun pool : SpacePool kind => pool .classicalBits)
    (EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace_eq_bits
      kind fieldWidth sampleWidth)

private lemma nearestScratch_classical_bound (kind : ProblemKind)
    (fieldWidth sampleWidth fieldCeiling sampleCeiling : Nat)
    (field : signedWidth fieldWidth ≤ fieldCeiling)
    (sample : signedWidth sampleWidth ≤ sampleCeiling) :
    EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace
      kind fieldWidth sampleWidth .classicalBits ≤
      max (27 * sampleWidth + 9 * sampleCeiling + 17)
        (27 * fieldWidth + 9 * fieldCeiling + 15) :=
  (nearestScratch_classical_evaluation kind fieldWidth sampleWidth).le.trans
    (max_le_max
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 9 sample) _) _)
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 9 field) _) _))

private lemma runAdditional_evaluation (axis : SpaceAxis .quantum) :
    runAdditionalSpace axis = max (samplerAdditionalSpace axis)
      (EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace
        .quantum 256 260 axis) :=
  congrArg (fun pool : SpacePool .quantum => pool axis) runAdditional_canonical

/-- Successive table and nearest-checking scopes share their actual lexical maximum. -/
lemma runAdditional_classical_le : runAdditionalSpace .classicalBits ≤ 85079359 := by
  have tail := nearestScratch_classical_bound .quantum 256 260 132358 136506
    fieldSignedWidth_le sampleSignedWidth_le
  have tailBound : EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace
      .quantum 256 260 .classicalBits ≤ 85079359 := tail.trans (by decide)
  exact (runAdditional_evaluation .classicalBits).le.trans
    (max_le samplerAdditional_classical_le tailBound)

/-- The same run retains every original resident bit beside its 1037 persistent bits. -/
lemma run_resident_classical_numeric_le
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakResidentSpace path .classicalBits ≤
      85080396 + ctx.residentSpace .classicalBits := by
  have actual := original.run_resident_le (services := services) path .classicalBits
  have extra := runAdditional_classical_le
  rw [EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits] at actual
  change _ ≤ runAdditionalSpace .classicalBits + 1037 +
    ctx.residentSpace .classicalBits at actual
  omega

/-- Every original auxiliary role is retained beside the same lexical classical ceiling. -/
lemma run_auxiliary_classical_numeric_le
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakAuxiliarySpace path .classicalBits ≤
      85080396 + ctx.auxiliarySpace .classicalBits := by
  have actual := original.run_auxiliary_le (services := services) path .classicalBits
  have extra := runAdditional_classical_le
  rw [EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits] at actual
  change _ ≤ runAdditionalSpace .classicalBits + 1037 +
    ctx.auxiliarySpace .classicalBits at actual
  omega

private lemma shapeList_quantum (shapes : List CShape) (dimension : ℕ+) :
    ((shapes.map (SpacePool.ofShape (kind := .quantum))).sum) (.quantumSystems dimension) = 0 := by
  induction shapes with
  | nil => rfl
  | cons head rest ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_apply, SpacePool.ofShape,
        Nat.zero_add] using ih

/-- The actual table and arithmetic construction cells add no quantum system. -/
lemma samplerAdditional_quantumSystems (dimension : ℕ+) :
    samplerAdditionalSpace (.quantumSystems dimension) = 0 := by
  simp [samplerAdditionalSpace, EllipticCurve.WindowTables.Outer.tableSpace_quantumSystems,
    EllipticCurve.WindowTables.Outer.coefficientScratchSpace,
    EllipticCurve.Field.Native.coefficientActiveSpace, rawScratchSpace,
    signedReductionSpaceLimit, signedReductionScratchSpace, signedReductionArithmeticSpace,
    negativeCorrectionScratchSpace, SpacePool.max, SpacePool.ofShape, shapeList_quantum]

/-- The nearest checker and final option packing also allocate only classical cells. -/
lemma runAdditional_quantumSystems (dimension : ℕ+) :
    runAdditionalSpace (.quantumSystems dimension) = 0 := by
  rw [runAdditional_canonical,
    EllipticCurve.CandidateCheck.Native.Nearest.recoveryTailScratchSpace_eq_bits]
  simp only [SpacePool.max, samplerAdditional_quantumSystems, SpacePool.ofShape,
    Nat.max_self]

/-- The exact actual resident quantum peak is the supplied caller's peak in every dimension. -/
lemma run_resident_quantumSystems (dimension : ℕ+)
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakResidentSpace path
      (.quantumSystems dimension) = ctx.residentSpace (.quantumSystems dimension) := by
  apply le_antisymm
  · have actual := original.run_resident_le (services := services) path
      (.quantumSystems dimension)
    simpa only [Pi.add_apply, runAdditional_quantumSystems,
      EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits, SpacePool.ofShape,
      Nat.zero_add] using actual
  · exact (original.run (services := services)).code.input_residentSpace_le_peak path
      (.quantumSystems dimension)

/-- The same exact equality preserves all original quantum auxiliary roles. -/
lemma run_auxiliary_quantumSystems (dimension : ℕ+)
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakAuxiliarySpace path
      (.quantumSystems dimension) = ctx.auxiliarySpace (.quantumSystems dimension) := by
  apply le_antisymm
  · have actual := original.run_auxiliary_le (services := services) path
      (.quantumSystems dimension)
    simpa only [Pi.add_apply, runAdditional_quantumSystems,
      EllipticCurve.CandidateCheck.Native.persistentCellSpace_eq_bits, SpacePool.ofShape,
      Nat.zero_add] using actual
  · exact (original.run (services := services)).code.input_auxiliarySpace_le_peak path
      (.quantumSystems dimension)

end Recovery.Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
