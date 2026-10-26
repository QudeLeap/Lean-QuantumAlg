/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Recovery.Cells
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Correctness
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Decode
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Inputs

/-!
# Original recoverable Fourier events imply the existing nearest predicate

The actual paid input is reindexed by its proved width equality, preserving every
bit. The original nearest-recovery theorem then gives the exact candidate word
and both success flags. No additional decoder invocation or point-port premise
is needed for this observable inclusion.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution ClassicalWorkspace
open PrimeFieldShortWeierstrass FiniteCyclicDLP ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open FiniteCyclicDLP.Canonical.Probability (SecretInput residueIndex)
open ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery

/-- Full raw structures transport by equality of widths and equality of every bit. -/
private lemma preparationInput_width_cast {first last : Nat} (same : first = last)
    (sample : CShape.Value (.fixedVector (last + last) (.finite 2)))
    (original : Fin (2 * first) → Bool)
    (bits : (fun index : Fin (2 * first) =>
      (Native.measuredDecodeInput sample).bits
        (Fin.cast (two_mul last)
          (Fin.cast (congrArg (fun width : Nat => 2 * width) same) index))) = original) :
    Native.preparationInput sample =
      cast (congrArg (fun width : Nat => CShape.Value (InputShape width)) same)
        (.bits (fun index => original (Fin.cast (two_mul first).symm index))) := by
  cases same
  apply congrArg CShape.Value.bits
  funext index
  exact congrFun bits (Fin.cast (two_mul first).symm index)

/-- Width equality reuses the old theorem for the actual modulus specification. -/
private lemma nearest_outputCells_width_transport
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (problem : KnownOrderProblem E.GroupPoint) (prime : problem.order.Prime)
    (input : SecretInput problem) {width : Nat} (same : orderWidth problem = width)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (accepted : EllipticCurve.FullRange.recoverableExponentEvent problem input bits = true)
    (spec : ModulusSpec width) (sameOrder : spec.modulus = problem.order)
    (raw : CShape.Value (InputShape width))
    (sameRaw : raw =
      cast (congrArg (fun n : Nat => CShape.Value (InputShape n)) same)
        (rawExponentInput problem bits)) :
    Nearest.outputCellsInput spec raw =
      .product (.bit true)
        (.product (CShape.wordOfNat width input.secret.val) (.bit true)) := by
  cases same
  rw [sameRaw]
  exact EllipticCurve.FullRange.nearest_outputCells_recoverableEvent
    problem prime input bits accepted spec sameOrder

/-- The equal numeric pair shapes preserve every bit after the width cast. -/
private lemma double_cast_260 (width : Nat) (same : width = 260)
    (bits : Fin (260 + 260) → Bool) :
    (fun index : Fin (2 * width) => bits (Fin.cast (two_mul 260)
      (Fin.cast (congrArg (fun count : Nat => 2 * count) same) index))) =
    (fun index : Fin (2 * width) => bits
      (Fin.cast (congrArg (fun count : Nat => 2 * count) same) index)) := by
  rfl

/-- The actual paid preparation has the complete original raw input value. -/
lemma pairedInput_original_raw {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) :
    Native.preparationInput (store.read (Sampling.Recovery.pairedInput parameters)) =
      cast (congrArg (fun width : Nat => CShape.Value (InputShape width))
          (Cascade.exponentWidth_eq_260 I))
        (rawExponentInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
          (ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
            (decodedFrequency I (storedComplete parameters store)))) := by
  have bits := (double_cast_260 (Cascade.exponentWidth I) (Cascade.exponentWidth_eq_260 I)
    (Native.measuredDecodeInput
      (store.read (Sampling.Recovery.pairedInput parameters))).bits).trans
      (pairedInput_original_bits parameters I store)
  have result := @preparationInput_width_cast (Cascade.exponentWidth I) 260
    (Cascade.exponentWidth_eq_260 I)
    (store.read (Sampling.Recovery.pairedInput parameters))
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
      (decodedFrequency I (storedComplete parameters store))) bits
  exact result

/-- Both flags and the exact secret word are those of the one actual nearest invocation. -/
lemma pairedInput_nearest_outputCells {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (spec : ModulusSpec 260) (sameOrder : spec.modulus = DomainParameters.subgroupOrder)
    (store : Store ctx)
    (accepted : EllipticCurve.FullRange.recoverableExponentEvent
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
        (decodedFrequency I (storedComplete parameters store))) = true) :
    Nearest.outputCellsInput spec
        (Native.preparationInput (store.read (Sampling.Recovery.pairedInput parameters))) =
      .product (.bit true) (.product (CShape.wordOfNat 260 input.secret.val) (.bit true)) := by
  exact nearest_outputCells_width_transport
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime input
    (Cascade.exponentWidth_eq_260 I) _ accepted spec sameOrder _
    (pairedInput_original_raw parameters I store)

/-- Exact output cells determine the natural scalar and both flags. -/
private def CandidateConditionStatement (Point : Type*) [SMul Nat Point] : Prop :=
  ∀ {scalarWidth : Nat} (basePoint targetPoint : Point)
    (raw : CShape.Value (.product .bit (.product (.unsignedWord scalarWidth) .bit)))
    (secret : Nat) (_fits : secret < 2 ^ scalarWidth)
    (_pointEquation : secret • basePoint = targetPoint)
    (_cells : raw =
      .product (.bit true) (.product (CShape.wordOfNat scalarWidth secret) (.bit true))),
    raw.second.first.toNat • basePoint = targetPoint ∧
      raw.first.toBool = true ∧ raw.second.second.toBool = true

/-- Exact decoder cells imply the candidate condition for any natural scalar action. -/
private lemma candidateCondition_of_exact_cells {Point : Type*} [SMul Nat Point] :
    CandidateConditionStatement Point := by
  intro scalarWidth basePoint targetPoint raw secret fits pointEquation cells
  rw [cells]
  change (secret % 2 ^ scalarWidth) • basePoint = targetPoint ∧ true = true ∧ true = true
  refine ⟨?_, rfl, rfl⟩
  exact (congrArg (fun scalar : Nat => scalar • basePoint)
    (Nat.mod_eq_of_lt fits)).trans pointEquation

/-- The original paid-input event implies the actual nearest candidate predicate. -/
private def PairedInputAcceptedStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (spec : ModulusSpec 260) (_sameOrder : spec.modulus = DomainParameters.subgroupOrder)
    (store : Store ctx)
    (_accepted : EllipticCurve.FullRange.recoverableExponentEvent
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
      (fun position : Fin (2 * Cascade.exponentWidth I) =>
        (Native.measuredDecodeInput
          (store.read (Sampling.Recovery.pairedInput parameters))).bits
            (Fin.cast (congrArg (fun width : Nat => 2 * width)
              (Cascade.exponentWidth_eq_260 I)) position)) = true),
    CandidateCheck.Native.Nearest.SampleAccepted (actualCurveSpec I) spec
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      (store.read (Sampling.Recovery.pairedInput parameters))

private lemma pairedInputAcceptedStatement_proof : PairedInputAcceptedStatement := by
  intro ctx parameters I input spec sameOrder store accepted
  let : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have fits : input.secret.val < 2 ^ Cascade.exponentWidth I :=
    lt_of_lt_of_le (residueIndex _ input.secret).isLt (order_le_fourierModulus _)
  rw [Cascade.exponentWidth_eq_260] at fits
  have equation := secret_groupScalar_eq_target
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
  have eventSame := congrArg
    (EllipticCurve.FullRange.recoverableExponentEvent
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input)
    (pairedInput_original_bits parameters I store)
  unfold CandidateCheck.Native.Nearest.SampleAccepted
  exact candidateCondition_of_exact_cells _ _ _ input.secret.val fits
    equation (pairedInput_nearest_outputCells parameters I input spec sameOrder store
      (eventSame.symm.trans accepted))

/-- The existing recoverable event implies the actual predicate, at the fitted order width. -/
lemma pairedInput_sampleAccepted {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (spec : ModulusSpec 260) (sameOrder : spec.modulus = DomainParameters.subgroupOrder)
    (store : Store ctx)
    (accepted : EllipticCurve.FullRange.recoverableExponentEvent
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
      (fun position : Fin (2 * Cascade.exponentWidth I) =>
        (Native.measuredDecodeInput
          (store.read (Sampling.Recovery.pairedInput parameters))).bits
            (Fin.cast (congrArg (fun width : Nat => 2 * width)
              (Cascade.exponentWidth_eq_260 I)) position)) = true) :
    CandidateCheck.Native.Nearest.SampleAccepted (actualCurveSpec I) spec
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      (store.read (Sampling.Recovery.pairedInput parameters)) := by
  exact pairedInputAcceptedStatement_proof parameters I input spec sameOrder store accepted

/-- The actual retained/feedback transports retain the same order and nearest operand. -/
lemma factory_currentSampleAccepted {outer inner : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) :
    let original := Factory.inputs I sameWires results frame base target
    let retained := original.transport (Sampling.Recovery.persistentTransport outer)
      (Sampling.Recovery.persistent_wires outer)
    let current := retained.transport lift same
    let sampler := retained.samplerParameters lift same scratch fresh
    ∀ store : Store inner,
      EllipticCurve.FullRange.recoverableExponentEvent
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
        (fun position : Fin (2 * Cascade.exponentWidth I) =>
          (Native.measuredDecodeInput
            (store.read (Sampling.Recovery.pairedInput sampler))).bits
              (Fin.cast (congrArg (fun width : Nat => 2 * width)
                (Cascade.exponentWidth_eq_260 I)) position)) = true →
      CandidateCheck.Native.Nearest.SampleAccepted current.curve current.order
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
        (store.read (Sampling.Recovery.pairedInput sampler)) := by
  intro original retained current sampler store accepted
  have modulus : current.order.modulus = DomainParameters.subgroupOrder :=
    Factory.inputs_order I sameWires results frame base target
  exact pairedInput_sampleAccepted sampler I input current.order modulus store accepted

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
