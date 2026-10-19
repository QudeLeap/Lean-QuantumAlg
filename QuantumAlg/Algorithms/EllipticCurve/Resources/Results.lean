/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.FullRun
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Algorithms.EllipticCurve.Resources
import all QuantumAlg.Core.Execution.Input.Oracle.Empty
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.FullRun
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.EventCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Bounds
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Events

/-!
# Same-run generic ECDLP correctness and all seven scalar coordinates

The named solver uses exactly the actual streaming execution of the public
existential main. The reduced quantum bank and six other independent scalar ceilings apply to
the same complete Path. Quantum time uses the independent reset/sampling formula; the
separate unit-duration event bound charges the actual initial bank and final
pack even at zero retries. No original 607-event allowance pays for 818 bank
preparations.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract

attribute [local irreducible] run

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The native problem has no additional hidden specification datum. -/
public def unitWitness (I : ECDLPInstance E) (count : Nat) (failure : ℝ) :
    (problem E I count failure).Witness := ()

/-- Encode the original public points while retaining an arbitrary quantum reference input. -/
public def sourceInput (I : ECDLPInstance E) {Reference : Register}
    (original : Input (Execution.inputContext E I) Reference) :
    OracleInput .empty (Execution.inputContext E I) Reference :=
  OracleInput.withEmptyService (ECDLP.Measured.Recovery.PublicInput.Support.prescribedInput
    E (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I) original)

private lemma input_eq_of_state_eq {ctx : RuntimeCtx .quantum} {Reference : Register}
    (first second : Input ctx Reference) (same : first.state = second.state) : first = second := by
  cases first
  cases second
  cases same
  rfl

omit [Fact p.Prime] in
/-- Every original public-point encoding is admitted under every interpreter environment. -/
public lemma source_admits (I : ECDLPInstance E) (count : Nat) (failure : ℝ)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (Execution.inputContext E I) Reference) :
    (problem E I count failure).Admits environment (unitWitness E I count failure)
      (sourceInput E I original) := by
  refine ⟨?_, trivial⟩
  change ECDLP.Measured.Recovery.PublicInput.Support.inputDomain E
    (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I)
      (sourceInput E I original).caller.localState
  have sameCaller : (sourceInput E I original).caller =
      ECDLP.Measured.Recovery.PublicInput.Support.prescribedInput E
        (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I) original := by
    apply input_eq_of_state_eq
    exact OracleInput.oracleInput_withEmptyService_caller_state
      (ctx := Execution.inputContext E I) (Reference := Reference)
      (ECDLP.Measured.Recovery.PublicInput.Support.prescribedInput E
        (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I) original)
  rw [sameCaller]
  exact ECDLP.Measured.Recovery.PublicInput.Support.inputDomain_prescribedInput
    E (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I) original

omit [Fact p.Prime] in
/-- Original public points satisfy validity in every interpreter environment. -/
public lemma source_valid (I : ECDLPInstance E) (count : Nat) (failure : ℝ)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (Execution.inputContext E I) Reference) :
    (problem E I count failure).valid environment (unitWitness E I count failure)
      (sourceInput E I original).caller.localState :=
  (source_admits E I count failure environment original).1

omit [Fact p.Prime] in
/-- Source callers satisfy initialization before the fixed native run. -/
public lemma source_initialized (I : ECDLPInstance E) (count : Nat) (failure : ℝ)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (Execution.inputContext E I) Reference) :
    (problem E I count failure).initialization environment (unitWitness E I count failure)
      (sourceInput E I original).localState :=
  (source_admits E I count failure environment original).2

/-- The same actual run solves the original problem under its complete error/retry condition. -/
public lemma algorithm_solves (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).Solves
      (problem E I count failure) :=
  complete_correct E fieldTail sameWidth fits odd I points seed addends count failure calibrated


variable (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
  (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
  (seed : AffinePoint E) (addends : AddendEncoding E I points)
  (count : Nat) (failure : ℝ)

/-- Seven parameter-only ceilings on the same actual ECC execution path.
Both classical storage roles and every quantum dimension remain explicit. -/
@[expose] public def SevenCoordinateBounds
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    Prop :=
  (∀ dimension : ℕ+,
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakResidentSpace
      path (.quantumSystems dimension) ≤
        if 2 = dimension then Scalar.streamingQubits p.size
        else 0) ∧
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakAuxiliarySpace
      path (.quantumSystems dimension) ≤
        if 2 = dimension then Scalar.streamingQubits p.size
        else 0)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .toffoli)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        count * Scalar.roundToffoli p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .cnot)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        count * Scalar.roundCnot p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .singleQubit)
      ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
        Scalar.loadBits p.size +
          count * Scalar.roundSingle p.size (orderWidth (ECDLP.Canonical.problem I)) ∧
  (algorithm E fieldTail sameWidth fits odd I points seed count).quantumTime path ≤
    Scalar.quantumTime p.size (orderWidth (ECDLP.Canonical.problem I)) count ∧
  (((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakResidentSpace
      path .classicalBits ≤ Scalar.residentBits p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I))) ∧
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.peakAuxiliarySpace
      path .classicalBits ≤ Scalar.auxiliaryBits p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm E fieldTail sameWidth fits odd I points seed count).run.code.resourcePool path) ≤
      count * Scalar.recoveryEvents (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)) + 1

private lemma quantumTime_formula (width samples attempts : Nat) :
    attempts * ((Recovery.Layout.terminal width samples).systemCount +
      (4 * MAU.Multiplication.Gidney.eventBound width +
        2 * samples * (MeasuredPointAddition.depthBound width + 2 * samples + 13))) =
      Scalar.quantumTime width samples attempts := by
  simp only [Events.terminal_systemCount, Scalar.multiplierTime_eq, Scalar.pointDepth_eq,
    Scalar.quantumTime, Scalar.streamingQubits, Recovery.PublicInput.Allocation.Events.bankWidth]

/-- The reduced bank and all six remaining scalar ceilings hold on every actual Path. -/
public lemma algorithm_sevenCoordinates
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    SevenCoordinateBounds E fieldTail sameWidth fits odd I points seed count path := by
  dsimp only [SevenCoordinateBounds, algorithm, Execution.inputContext, Execution.outputContext,
    Spec.inputContext, Spec.outputContext]
  have gateBound := EventCoordinates.run_gate_count_le E (ECDLP.Canonical.problem I)
    fieldTail points seed I.subgroupOrder (Semantics.radixUnit p fieldTail.succ odd)
    I.subgroupOrder_prime.two_le count path
  have classical := Coordinates.run_classical_space_scalar_le E fieldTail
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder
    (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le count path
  have native := Coordinates.run_classicalOperations_le E fieldTail
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder
    (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le count path
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    exact Coordinates.run_quantumSystems_both_le E fieldTail
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder
      (Semantics.radixUnit p fieldTail.succ odd) I.subgroupOrder_prime.two_le count path dimension
  · apply (gateBound .toffoli).trans_eq
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_toffoli_count]
  · apply (gateBound .cnot).trans_eq
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_cnot_count]
  · apply (gateBound .singleQubit).trans
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_single_count]
    exact Nat.le_add_left
      (count * Scalar.roundSingle p.size (orderWidth (ECDLP.Canonical.problem I)))
      (Scalar.loadBits p.size)
  · apply (Bounds.run_quantumTime_le E fieldTail (ECDLP.Canonical.problem I)
      points seed I.subgroupOrder (Semantics.radixUnit p fieldTail.succ odd)
      I.subgroupOrder_prime.two_le count path).trans_eq
    exact quantumTime_formula _ _ _
  · exact classical
  · exact native

/-- Independent chronological depth pays for the actual bank also at zero retries. -/
public lemma algorithm_wholeRunDepth_scalar
    (path : (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.Path) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).run.code.depth
        (fun _ => 1) path ≤
      Scalar.streamingWholeRunEvents p.size (Nat.clog 2 p)
        (orderWidth (ECDLP.Canonical.problem I)) count :=
  streaming_run_unitDepth_scalar E fieldTail (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder (Semantics.radixUnit p fieldTail.succ odd)
    I.subgroupOrder_prime.two_le count path

end

end QuantumAlg.EllipticCurve.LogicalResources
