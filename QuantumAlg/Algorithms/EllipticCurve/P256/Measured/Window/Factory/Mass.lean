/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Observation
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Prepared
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Window
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prepared.Restart
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Lower
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Conditional

/-!
# The actual factory discharges its internal candidate-mass obligation

The literal sampler lower bound is lifted through the actual measured restart.
No caller quality, normalization or round independence premise is added.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open FiniteCyclicDLP.Canonical.Probability (SecretInput)
open ClassicalAlgorithms.EllipticCurve ClassicalRoutines.EllipticCurve

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma positive_before_selection {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (read : Record → Bool) (flag : Bool)
    (record : Record)
    (positive : 0 < ((state.selectClassical read flag).block record).mass) :
    0 < (state.block record).mass := by
  by_cases selected : read record = flag
  · simpa only [ExecutionState.selectClassical_block, if_pos selected] using positive
  · have impossible : (0 : ℝ) < 0 := by
      simpa only [ExecutionState.selectClassical_block, if_neg selected,
        DensityOperator.zero_mass] using positive
    exact False.elim (lt_irrefl _ impossible)

private lemma pure_lower_seed_transport {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (firstDecision lastDecision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (record : Store ctx × (services.HiddenState × History))
    {Reference : Register} (reference : NormalizedVector Reference)
    (event : Store ctx → Effect (ctx.register.prod Reference)) (lower : ℝ)
    (actual source : ctx.register.Index) (same : actual = source)
    (bound : lower ≤ storeEffectWeight code environment
      (@ExecutionState.ofValue _ _ _ firstDecision record (DensityOperator.ofPure
        (NormalizedVector.prodTensor (NormalizedVector.ket source) reference))) event) :
    lower ≤ storeEffectWeight code environment
      (@ExecutionState.ofValue _ _ _ lastDecision record (DensityOperator.ofPure
        (NormalizedVector.prodTensor (NormalizedVector.ket actual) reference))) event := by
  cases same
  cases Subsingleton.elim lastDecision firstDecision
  exact bound

private lemma current_restart_seed {outer inner : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) (output : CWriteRef inner (.finite 2)) :
    let original := inputs I sameWires results frame base target
    let retained := original.transport (Sampling.Recovery.persistentTransport outer)
      (Sampling.Recovery.persistent_wires outer)
    let current := retained.transport lift same
    let sampler := retained.samplerParameters lift same scratch fresh
    current.restartSeed output = sampler.physicalLabel
      (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        (FullRange.chronologicalFixedSeed I) (false, false, false) 0) := by
  intro original retained current sampler
  exact physicalSeed_affine (current.restartCleanup output) sampler
    (actualCurveSpec I) (actualCurveSpec_modulus I) (FullRange.chronologicalFixedSeed I)

private def CurrentReferenceLowerStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) (output : CWriteRef inner (.finite 2))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (decision : DecidableEq (Store inner × (services.HiddenState × History)))
    (record : Store inner × (services.HiddenState × History))
    {Reference : Register} (reference : NormalizedVector Reference),
    let original := inputs I sameWires results frame base target
    let current := original.currentInput lift same
    let sampler := original.currentSampler lift same scratch fresh
    Good.Prepared sampler I record.1 →
      (4 : ℝ) / 5 ≤ storeEffectWeight (Sampling.circuit sampler) environment
        (@ExecutionState.ofValue _ _ _ decision record (DensityOperator.ofPure
          (NormalizedVector.prodTensor
            (NormalizedVector.ket (current.restartSeed output)) reference)))
        (recordEventEffect (inner.register.prod Reference)
          (Good.recoverableSourceEvent sampler I input))

private lemma currentReferenceLower_proof : CurrentReferenceLowerStatement := by
  intro outer inner services I sameWires results frame base target input lift same scratch fresh
    output environment History finite decision record Reference reference original current sampler
    prepared
  have source := Good.sampling_circuit_reference_lower (services := services) sampler I
    (by rfl) scratch
    (fun position => Good.sampler_point_references original.retainedInput lift same scratch fresh
      (Sampling.chronologicalIndex position)) environment record prepared input reference
  exact pure_lower_seed_transport (services := services) (Sampling.circuit sampler)
    environment _ decision record reference
    (recordEventEffect (inner.register.prod Reference)
      (Good.recoverableSourceEvent sampler I input)) ((4 : ℝ) / 5)
    (current.restartSeed output) _
    (current_restart_seed I sameWires results frame base target lift same scratch fresh output)
    source

private def CurrentMixedLowerStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    let original := inputs I sameWires results frame base target
    let current := original.currentInput lift same
    let sampler := original.currentSampler lift same scratch fresh
    (∀ record, 0 < (state.block record).mass → Good.Prepared sampler I record.1) →
      ((4 : ℝ) / 5) * state.mass ≤
        storeEffectWeight (current.preparation sampler) environment state
          (recordEventEffect (inner.register.prod Reference)
            (Good.recoverableSourceEvent sampler I input))

private lemma currentMixedLower_proof : CurrentMixedLowerStatement := by
  intro outer inner services I sameWires results frame base target input lift same scratch fresh
    environment Reference History finite state original current sampler prepared
  have restartedPrepared :
      ∀ record : Store inner × (services.HiddenState ×
        (History × (current.restart (services := services) (sampler.output 0)).Path)),
        0 < (current.restartBlock (sampler.output 0) environment state record).mass →
        Good.Prepared sampler I record.1 :=
    Good.restart_preserves_prepared (services := services) current sampler I
      (sampler.output 0) environment state prepared
  apply current.restart_then_observed_lower (services := services) (sampler.output 0)
    (Sampling.circuit sampler) environment state
    (recordEventEffect (inner.register.prod Reference)
      (Good.recoverableSourceEvent sampler I input)) ((4 : ℝ) / 5)
  intro record positive reference
  exact currentReferenceLower_proof (services := services) I sameWires results frame base target
    input lift same scratch fresh (sampler.output 0) environment _ record reference
    (restartedPrepared record positive)

private def FactoryCandidateMassStatement : Prop :=
  ∀ {outer : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (_input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment),
    let original := inputs I sameWires results frame base target
    original.InternalCandidateMass environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      ((4 : ℝ) / 5)

private lemma factoryCandidateMass_proof : FactoryCandidateMassStatement := by
  intro outer services I sameWires results frame base target input environment original inner lift
    same scratch fresh Reference History finite state supported
  let current := original.currentInput lift same
  let sampler := original.currentSampler lift same scratch fresh
  let checkers := Sampling.Storage.Inputs.currentCheckers lift
  let accepted := Sampling.Storage.Inputs.currentAccepted lift
  let selected := state.selectClassical (fun record =>
    Sampling.Storage.flagInputRead accepted record.1) false
  have prepared : ∀ record, 0 < (selected.block record).mass →
      Good.Prepared sampler I record.1 := by
    intro record positive
    exact current_sampler_prepared_of_readConditions I sameWires results frame base target
      lift same scratch fresh record.1
      (supported record (positive_before_selection state _ false record positive))
  have lower := currentMixedLower_proof (services := services) I sameWires results frame base target
    input lift same scratch fresh environment selected prepared
  change ((4 : ℝ) / 5) * Sampling.Storage.CheckerTail.readWeight state
      (Sampling.Storage.flagInputRead accepted) false ≤
    Sampling.Storage.CheckerTail.readWeight
      ((current.preparation sampler).execute environment Reference selected)
      ((current.checkerTail sampler checkers).eligibleBit
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib) true
  calc
    _ = ((4 : ℝ) / 5) * selected.mass := congrArg (fun mass : ℝ => ((4 : ℝ) / 5) * mass)
      (Sampling.Storage.read_weight_selected_mass state
        (Sampling.Storage.flagInputRead accepted) false)
    _ ≤ _ := lower
    _ ≤ _ := current_recoverableWeight_le_eligible I sameWires results frame base target input
      lift same scratch fresh checkers
      ((current.preparation sampler).execute environment Reference selected)

/-- The actual factory supplies its own four-fifths candidate mass on all admitted states. -/
lemma factory_internalCandidateMass {outer : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    let original := inputs I sameWires results frame base target
    original.InternalCandidateMass environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      ((4 : ℝ) / 5) :=
  factoryCandidateMass_proof I sameWires results frame base target input environment

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
