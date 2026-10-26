/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation.Monotone
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Nearest
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Acceptance

/-!
# Original recoverable events imply actual factory nearest eligibility

This observes the same returned execution state and its existing paid paired
operand. Pointwise recovery implies the unchanged nearest checker's eligibility,
so the actual block observation weight can only increase.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open FiniteCyclicDLP.Canonical.Probability (SecretInput)
open ClassicalAlgorithms.EllipticCurve ClassicalRoutines.EllipticCurve

/-- The exact actual paired operand event is included in the unchanged nearest eligibility. -/
lemma current_recoverableWeight_le_eligible {outer inner : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer)
    (frame : WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift)
    (checkers : Sampling.Storage.Checkers inner)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference History) :
    let original := inputs I sameWires results frame base target
    let retained := original.transport (Sampling.Recovery.persistentTransport outer)
      (Sampling.Recovery.persistent_wires outer)
    let current := retained.transport lift same
    let sampler := retained.samplerParameters lift same scratch fresh
    let event : Store inner → Bool := fun store =>
      EllipticCurve.FullRange.recoverableExponentEvent
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
        (fun position : Fin (2 * Cascade.exponentWidth I) =>
          (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
            (store.read (Sampling.Recovery.pairedInput sampler))).bits
              (Fin.cast (congrArg (fun width : Nat => 2 * width)
                (Cascade.exponentWidth_eq_260 I)) position))
    state.effectWeight
        (fun record => recordEventEffect (inner.register.prod Reference) event record.1) ≤
      Sampling.Storage.CheckerTail.readWeight state
        ((current.checkerTail sampler checkers).eligibleBit
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib)
        true := by
  intro original retained current sampler event
  change state.effectWeight
      (recordEventEffect (inner.register.prod Reference) (fun record => event record.1)) ≤
    state.effectWeight
      (recordEventEffect (inner.register.prod Reference) (fun record =>
        (current.checkerTail sampler checkers).eligibleBit
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib
          I.publicKey.toMathlib record.1))
  apply recordEvent_effectWeight_mono
  intro record selected
  apply ((current.checkerTail sampler checkers).eligibleBit_true
    (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib record.1).2
  exact Good.factory_currentSampleAccepted I sameWires results frame base target input
    lift same scratch fresh record.1 selected

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
