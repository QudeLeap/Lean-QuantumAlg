/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Resources
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Memory, classical operations and absent queries of the same streaming run

These results concern the literal allocated run and every complete Path. The
resident and auxiliary quantum coordinates retain every physical dimension;
the classical coordinates retain both borrowed public points, all seven
persistent destinations and the maximum of the reused lexical scratch.

Classical work follows the actual allocation, every sampling/checking attempt
and the one final paid option pack. The promoted quantum instructions have
zero classical-operation weight. The complete native checker keeps its original
independent allowance. Neither quantum nor classical oracle access is granted.

 It does not assert native
gate counts, a complete event-pool budget, endpoint success or Algorithm.Solves.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Coordinates

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.ClassicalAlgorithms.EllipticCurve QuantumAlg.ClassicalAlgorithms.Modular
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open FiniteCyclicDLP
open scoped BigOperators

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model


private lemma signedWidth_scalar_le (width : Nat) :
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth width ≤
      LogicalResources.Scalar.coefficientBits width :=
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_le_quadratic (width + 1)

private lemma classicalWeight_le_card (pool : ResourcePool Model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bounded := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event Model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bounded

private lemma selected_classicalWeight_zero {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation)
    (path : (BitWord.selectForCircuit code).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((BitWord.selectForCircuit code).resourcePool path) = 0 := by
  let original := (BitWord.selectForCircuitPathEquiv code).symm path
  have originalPool := BitWord.selectForCircuit_resourcePool code original
  have selected : (BitWord.selectForCircuit code).resourcePool path =
      BitWord.liftQuantumPool (code.resourcePool original) :=
    (congrArg (fun selectedPath => (BitWord.selectForCircuit code).resourcePool selectedPath)
      ((BitWord.selectForCircuitPathEquiv code).apply_symm_apply path)).symm.trans originalPool
  rw [selected, BitWord.liftQuantumPool_weightedCount]
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event _present
  cases event with
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | gate coordinate => rfl
  | oracle coordinate => rfl
  | preparation dimension => rfl
  | measurement dimension => rfl

private lemma forRange_classicalWeight_le {ctx : RuntimeCtx Model.kind}
    {allowAllocation : Bool} (count : Nat)
    (body : Fin count → Circuit Model ctx ctx allowAllocation) (budget : Nat)
    (bounded : ∀ index path, ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((body index).resourcePool path) ≤ budget)
    (path : (Circuit.forRange count body).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Circuit.forRange count body).resourcePool path) ≤ count * budget := by
  induction count with
  | zero =>
      change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (0 : ResourcePool Model) ≤ 0 * budget
      simp
  | succ count ih =>
      change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.ofList ((body 0).eventTrace path.1 ++
          (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2)) ≤ _
      rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
      exact (Nat.add_le_add (bounded 0 path.1)
        (ih (fun index => body index.succ) (fun index => bounded index.succ) path.2)).trans_eq
          (by rw [Nat.succ_mul]; omega)

private lemma checker_classicalWeight_le {ctx : RuntimeCtx Model.kind}
    {width scalarWidth : Nat} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (path : (persistentAttempt curve modulus sample base target).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((persistentAttempt curve modulus sample base target).resourcePool path) ≤
        LogicalResources.Scalar.recoveryEvents width scalarWidth := by
  have native := ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path)
  exact native.trans ((classicalWeight_le_card _).trans
    (attemptEnvelope_card_le Model curve modulus))

private lemma classicalWeight_append (first second : List (Resource.Event Model)) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.ofList (first ++ second)) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (ResourcePool.ofList first) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (ResourcePool.ofList second) := by
  rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]

private lemma classicalWeight_seq {pre middle post : RuntimeCtx Model.kind}
    {allowAllocation : Bool} (first : Circuit Model pre middle allowAllocation)
    (second : Circuit Model middle post allowAllocation) (path : (first.seq second).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((first.seq second).resourcePool path) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (first.resourcePool path.1) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (second.resourcePool path.2) :=
  classicalWeight_append (first.eventTrace path.1) (second.eventTrace path.2)

private lemma sampledAttempt_classicalWeight_le {ctx : RuntimeCtx Model.kind}
    {width scalarWidth : Nat} (sampleCode : Circuit Model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (sampleZero : ∀ samplePath,
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (sampleCode.resourcePool samplePath) = 0)
    (path : (sampledAttempt sampleCode curve modulus sample base target).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((sampledAttempt sampleCode curve modulus sample base target).resourcePool path) ≤
        LogicalResources.Scalar.recoveryEvents width scalarWidth := by
  have trace := sampledAttempt_eventTrace sampleCode curve modulus sample base target path
  have split : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((sampledAttempt sampleCode curve modulus sample base target).resourcePool path) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (sampleCode.resourcePool path.1) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          ((persistentAttempt curve modulus sample base target).resourcePool path.2) :=
    (congrArg (fun events : List (Resource.Event Model) =>
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.ofList events)) trace).trans (classicalWeight_append _ _)
  have bounded := Nat.add_le_add (sampleZero path.1).le
    (checker_classicalWeight_le curve modulus sample base target path.2)
  exact split.le.trans (bounded.trans_eq (Nat.zero_add _))

private lemma sampledTail_classicalWeight_le {ctx : RuntimeCtx Model.kind}
    {width scalarWidth : Nat} (sampleCode : Circuit Model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (sampleZero : ∀ samplePath,
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (sampleCode.resourcePool samplePath) = 0)
    (path : (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((sampledRecoveryTail sampleCode count curve modulus sample base target).resourcePool path) ≤
        count * LogicalResources.Scalar.recoveryEvents width scalarWidth + 1 := by
  have loopBound := forRange_classicalWeight_le count
    (fun _ => sampledAttempt sampleCode curve modulus sample base target)
    (LogicalResources.Scalar.recoveryEvents width scalarWidth)
    (fun _ => sampledAttempt_classicalWeight_le sampleCode curve modulus sample base target
      sampleZero) path.1.2
  have trace := sampledRecoveryTail_eventTrace sampleCode count curve modulus sample base target
    path
  have split : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((sampledRecoveryTail sampleCode count curve modulus sample base target).resourcePool
          path) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          ((sampledAttempts sampleCode count curve modulus sample base target).resourcePool
            path.1.2) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := Model)
            (.nominalEncoding (.packOption scalarWidth)))]) :=
    (congrArg (fun events : List (Resource.Event Model) =>
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.ofList events)) trace).trans (classicalWeight_append _ _)
  have pack : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := Model)
        (.nominalEncoding (.packOption scalarWidth)))]) = 1 := by
    simp [Resource.Event.classicalOperationWeight]
  exact split.le.trans (Nat.add_le_add loopBound pack.le)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ) (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Auxiliary accounting retains the same live qubits in every physical dimension. -/
lemma run_auxiliary_quantumSystems_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      ((run E fieldTail problem points seed r coefficient
        nontrivial count).code.peakAuxiliarySpace path) ≤
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0 := by
  have bounded := SpacePool.le_iff_count.mp
    (run_auxiliary_le E fieldTail problem points seed r coefficient nontrivial count path)
    (.quantumSystems dimension)
  simpa only [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    SpacePool.count_add, SpacePool.count_quantumSystems_ofShape, zero_add,
    Recovery.PublicInput.context_auxiliary,
    (Recovery.Layout.streamingTerminal_quantumSystems p.size (orderWidth problem) dimension).2]
    using bounded

/-- Both actual storage roles satisfy the reduced qubit allowance on the same complete Path. -/
lemma run_quantumSystems_both_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakResidentSpace path) ≤
        (if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0) ∧
      SpacePool.count (.quantumSystems dimension)
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakAuxiliarySpace path) ≤
        (if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0) :=
  ⟨run_quantumSystems_le E fieldTail problem points seed r coefficient nontrivial count
      path dimension,
    run_auxiliary_quantumSystems_le E fieldTail problem points seed r coefficient nontrivial
      count path dimension⟩


/-- The actual resident and auxiliary peaks both use at most 818 qubits at field width 256. -/
lemma run_width256_quantumSystems_both_le (width : p.size = 256)
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    SpacePool.count (.quantumSystems 2)
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakResidentSpace path) ≤ 818 ∧
      SpacePool.count (.quantumSystems 2)
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakAuxiliarySpace path) ≤ 818 := by
  have both := run_quantumSystems_both_le E fieldTail problem points seed r coefficient
    nontrivial count path 2
  have arithmetic : 3 * (256 : Nat) + 4 * (256 : Nat).size + 14 = 818 := by decide
  simpa only [if_pos rfl, if_true, width, arithmetic] using both

omit [Fact p.Prime] in
/-- The complete public context has the original resident and auxiliary classical capacities. -/
lemma publicContext_classicalBits (m : Nat) :
    SpacePool.count .classicalBits (Recovery.PublicInput.context E m).residentSpace =
        p.size + 2 * m + 4 * ECDLP.Canonical.Layout.fieldWidth E + 2 ∧
      SpacePool.count .classicalBits (Recovery.PublicInput.context E m).auxiliarySpace =
        p.size + 2 * m := by
  constructor
  · rw [Recovery.PublicInput.context_resident, SpacePool.count_add,
      (Recovery.Layout.streamingTerminal_classicalBits p.size m).1]
    simp [SpacePool.count, SpacePool.ofShape, ECDLP.Canonical.Runtime.Context.PointShape,
      PointShape, CShape.bitWidth]; omega
  · rw [Recovery.PublicInput.context_auxiliary]
    exact (Recovery.Layout.streamingTerminal_classicalBits p.size m).2

/-- The original independent scalar classical ceilings cover the same complete streaming Path. -/
lemma run_classical_space_scalar_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    SpacePool.count .classicalBits
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakResidentSpace path) ≤
        LogicalResources.Scalar.residentBits p.size (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) ∧
      SpacePool.count .classicalBits
        ((run E fieldTail problem points seed r coefficient
          nontrivial count).code.peakAuxiliarySpace path) ≤
        LogicalResources.Scalar.auxiliaryBits p.size (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) := by
  have actual := run_classical_space_le E fieldTail problem points seed r coefficient
    nontrivial count path
  dsimp only at actual
  rw [(publicContext_classicalBits E (orderWidth problem)).1,
    (publicContext_classicalBits E (orderWidth problem)).2] at actual
  have field := signedWidth_scalar_le (ECDLP.Canonical.Layout.fieldWidth E)
  have sample := signedWidth_scalar_le (orderWidth problem)
  have scratch :
      max (25 * orderWidth problem +
          9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
            (orderWidth problem) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
            (ECDLP.Canonical.Layout.fieldWidth E) + 15) ≤
      LogicalResources.Scalar.scratchBits (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth problem) := by
    unfold LogicalResources.Scalar.scratchBits
    exact max_le_max (by omega) (by omega)
  unfold LogicalResources.Scalar.residentBits LogicalResources.Scalar.auxiliaryBits
  constructor <;> omega

/-- Every actual quantum sample contributes zero native classical-operation occurrences. -/
lemma round_classicalOperations_zero
    (path : (round E fieldTail problem points seed r coefficient).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((round E fieldTail problem points seed r coefficient).resourcePool path) = 0 :=
  selected_classicalWeight_zero _ path

/-- One genuine allocation, every complete checked attempt and the final paid pack are retained. -/
lemma run_classicalOperations_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run E fieldTail problem points seed r coefficient
        nontrivial count).code.resourcePool path) ≤
      count * LogicalResources.Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth problem) + 1 := by
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
  let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
  have allocation := selected_classicalWeight_zero
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)) path.1
  have tailBound := sampledTail_classicalWeight_le sampleCode count curve modulus sample base target
    (round_classicalOperations_zero E fieldTail problem points seed r coefficient) path.2
  have split := classicalWeight_seq
    (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
    (tailRun E fieldTail problem points seed r coefficient nontrivial count).code path
  exact split.le.trans ((Nat.add_le_add allocation.le tailBound).trans_eq (Nat.zero_add _))


end

end ExecutionContract.Coordinates
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
