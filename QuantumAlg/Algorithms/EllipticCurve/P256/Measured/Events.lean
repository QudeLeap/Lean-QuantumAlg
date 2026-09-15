/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Space
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cardinality

/-!
# Original P-256 native event and unit-depth coordinates

All formulas specialize the already certified repeated execution and its
independent native allowances. The original field width is 256 and both
exponents have width 260. A real reset has 4008 events, while its finite
branch allowance has 5344 entries. The two parallel inverse Fourier
transforms have 68120 events and unit depth 34060.

The remaining multiplier and measured point-addition terms keep their
original native event pools and depth formulas at width 256. They do not
represent a Toffoli conversion or an alternative circuit. Every complete
bound includes 4714 actual rounds, both initial preparations and the final
optional-result pack.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP ConcreteCircuitAccess
open ECDLP.Measured ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private theorem qubit_systems (ctx : RuntimeCtx .quantum)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2) :
    ctx.systemCount = ctx.residentSpace (.quantumSystems 2) := by
  rw [RuntimeCtx.residentSpace_quantumSystems]
  simp [QuantumLayout.dimensionCount, QuantumLayout.dimensions, qubits, List.ofFn_const]

/-- Every original resident quantum system is one of the 1336 actual reset wires. -/
theorem terminal_systemCount (I : DomainParameters.PublicKeyInstance) :
    (PublicInput.terminal (DomainParameters.curve I.curveCert)
      (orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))).systemCount = 1336 := by
  rw [qubit_systems _ (samplingReset_qubits _ _), LogicalResources.terminal_residentSpace]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, SpacePool.ofShape,
    ECDLP.Canonical.Runtime.Context.PointShape, ClassicalRoutines.EllipticCurve.PointShape,
    orderWidth_eq_260, fieldModulus_size]
  rfl

private theorem exponent_preparation_events {G : Type} [Group G] (problem : KnownOrderProblem G) :
    (exponentPreparationCircuit problem).eventCost.card = 2 := by
  simp [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost,
    rangePreparationCircuit_eventCost, ResourcePool.singleton]

private theorem exponent_preparation_depth {G : Type} [Group G] (problem : KnownOrderProblem G) :
    (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) = 1 := by
  simp [UnitaryCircuit.evaluatedEventDepth, exponentPreparationCircuit,
    pairConsecutiveCircuit_eventDepth, rangePreparationCircuit_eventDepth, DepthExpr.depthEval]

/-- Both original inverse Fourier transforms retain all of their native gate events. -/
theorem exponent_readout_events (I : DomainParameters.PublicKeyInstance) :
    (exponentReadoutCircuit (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).eventCost.card =
      68120 := by
  rw [exponentReadoutCircuit, pairConsecutiveCircuit_eventCost,
    UnitaryCircuit.dagger_eventCost, QFTCircuit_eventCost_eq, orderWidth_eq_260]
  simp [ResourcePool.singleton, Nat.choose_two_right]

/-- Parallel original exponent readouts retain the maximum of their identical serial depths. -/
theorem exponent_readout_unitDepth (I : DomainParameters.PublicKeyInstance) :
    (exponentReadoutCircuit (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))).evaluatedEventDepth
      (fun _ => 1) = 34060 := by
  change DepthExpr.depthEval (fun _ => 1) _ = _
  rw [exponentReadoutCircuit, pairConsecutiveCircuit_eventDepth]
  change max ((UnitaryCircuit.dagger (QFTCircuit _)).evaluatedEventDepth (fun _ => 1))
    ((UnitaryCircuit.dagger (QFTCircuit _)).evaluatedEventDepth (fun _ => 1)) = _
  rw [max_self, UnitaryCircuit.evaluatedEventDepth_dagger,
    QFTCircuit_evaluatedEventDepth_of_one, orderWidth_eq_260]

private theorem reset_wire_card {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (label : ctx.quantumLayout.Basis) :
    (resetWireBudget wire label).card = 2 + (ctx.quantumLayout.wire wire).dimension := by
  simp [resetWireBudget, ResourcePool.ofList, ResourcePool.singleton]

attribute [local irreducible] samplingReset

variable (I : DomainParameters.PublicKeyInstance)

/-- The branch pool includes both possible corrections, whereas each real wire chooses one. -/
theorem samplingResetBudget_card
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    (samplingResetBudget (DomainParameters.curve I.curveCert) 255
      (orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
      fieldTail_sameWidth fieldTail_fits seed).card = 5344 := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  simp only [samplingResetBudget, Multiset.card_sum, reset_wire_card, samplingReset_qubits]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    terminal_systemCount]
  rfl

/-- Actual reset traces and unit duration count exactly three native operations per wire. -/
theorem samplingReset_count_and_depth
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    ∀ (path : (samplingReset (DomainParameters.curve I.curveCert) 255
      (orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
      fieldTail_sameWidth fieldTail_fits seed).Path),
    ((samplingReset (DomainParameters.curve I.curveCert) 255
      (orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
      fieldTail_sameWidth fieldTail_fits seed).eventTrace path).length = 4008 ∧
    (samplingReset (DomainParameters.curve I.curveCert) 255
      (orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
      fieldTail_sameWidth fieldTail_fits seed).depth (fun _ => 1) path = 4008 := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  rw [samplingReset_eventCount, samplingReset_unitDepth, terminal_systemCount]
  exact ⟨rfl, rfl⟩

/-- One actual round uses the original four converters and 520 measured point calls. -/
theorem samplingRoundEventBound_eq :
    samplingRoundEventBound (DomainParameters.curve I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) =
      72650 + 4 * (MAU.Multiplication.Gidney.nativeBudget 256).card +
        520 * (MeasuredPointAddition.events 256).card := by
  rw [samplingRoundEventBound, terminal_systemCount]
  simp only [Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul,
    exponent_preparation_events, exponent_readout_events, orderWidth_eq_260,
    fieldModulus_size, ResourcePool.singleton, Multiset.card_replicate]
  omega

/-- The original parallel Fourier stages and serial reset remain distinct in unit depth. -/
theorem samplingRoundUnitDepth_eq :
    samplingRoundUnitDepth (DomainParameters.curve I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) =
      38589 + 4 * MAU.Multiplication.Gidney.eventBound 256 +
        520 * MeasuredPointAddition.depthBound 256 := by
  rw [samplingRoundUnitDepth, terminal_systemCount, exponent_preparation_depth,
    exponent_readout_unitDepth, orderWidth_eq_260, fieldModulus_size]
  omega

/-- The independent pool includes both reset corrections at every original qubit. -/
theorem samplingRoundBudget_card
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    (samplingRoundBudget (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      seed).card = 73986 + 4 * (MAU.Multiplication.Gidney.nativeBudget 256).card +
        520 * (MeasuredPointAddition.events 256).card := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  rw [samplingRoundBudget, Multiset.card_add, samplingResetBudget_card]
  simp only [Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul,
    exponent_preparation_events, exponent_readout_events, orderWidth_eq_260,
    fieldModulus_size, ResourcePool.singleton, Multiset.card_replicate]
  omega

/-- One actual original P-256 checked recovery has the certified complete native ceiling. -/
theorem attemptEnvelope_card_le_fixed :
    (attemptEnvelope .quantum
      (ECDLP.Canonical.Layout.curveSpec (DomainParameters.curve I.curveCert))
      (recoveryModulusSpec (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        I.subgroupCert.prime.two_le)).card ≤ 16685359 := by
  have bounded := attemptEnvelope_card_le .quantum
    (ECDLP.Canonical.Layout.curveSpec (DomainParameters.curve I.curveCert))
    (recoveryModulusSpec (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      I.subgroupCert.prime.two_le)
  conv at bounded => rhs; rw [orderWidth_eq_260, canonicalFieldWidth]
  exact bounded

/-- The original complete native allowance charges all branches, preparations and final pack. -/
theorem repeatedRunBudget_card_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    (repeatedRunBudget (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      seed I.subgroupCert.prime.two_le 4714).card ≤
      3 + 4714 * (16759345 + 4 * (MAU.Multiplication.Gidney.nativeBudget 256).card +
        520 * (MeasuredPointAddition.events 256).card) := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have checked := attemptEnvelope_card_le_fixed I
  simp only [repeatedRunBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.scale, Multiset.card_add, Multiset.card_nsmul,
    ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil,
    samplingRoundBudget_card]
  omega

attribute [local irreducible] exponentRepeatedRun

/-- All 4714 actual sampling and classical checking traces share the original complete bound. -/
theorem exponentRepeatedRun_eventCount_fixed_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    ∀ (path : (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.Path),
    ((exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.eventTrace path).length ≤
      3 + 4714 * (16758009 + 4 * (MAU.Multiplication.Gidney.nativeBudget 256).card +
        520 * (MeasuredPointAddition.events 256).card) := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  have bounded := exponentRepeatedRun_eventCount_le (DomainParameters.curve I.curveCert) 255
    fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
    I.subgroupCert.prime.two_le 4714 path
  conv at bounded => rhs; rw [samplingRoundEventBound_eq, orderWidth_eq_260, canonicalFieldWidth]
  refine bounded.trans_eq ?_
  omega

/-- The same execution keeps parallel Fourier depth and the original classical duration limit. -/
theorem exponentRepeatedRun_unitDepth_fixed_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    ∀ (path : (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.Path),
    (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.depth (fun _ => 1) path ≤
      3 + 4714 * (38589 + 4 * MAU.Multiplication.Gidney.eventBound 256 +
        520 * MeasuredPointAddition.depthBound 256 +
          attemptDepthLimit (kind := .quantum)
            (ECDLP.Canonical.Layout.curveSpec (DomainParameters.curve I.curveCert))
            (recoveryModulusSpec (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              I.subgroupCert.prime.two_le) (fun _ => 1)) := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  have bounded := exponentRepeatedRun_unitDepth_le (DomainParameters.curve I.curveCert) 255
    fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
    I.subgroupCert.prime.two_le 4714 path
  rw [samplingRoundUnitDepth_eq] at bounded
  refine bounded.trans_eq ?_
  omega

end

end QuantumAlg.EllipticCurve.P256.Measured
