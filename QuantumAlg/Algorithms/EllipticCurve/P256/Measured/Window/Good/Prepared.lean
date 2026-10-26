/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Inputs
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Specification.Read
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Inputs

/-!
# One shared preparation invariant throughout all actual windows

The four constants and both complete seventeen-row families are retained
together. Each next driver derives its selected row from this one invariant.
The literal zero-reset and every measured-middle record preserve it through
their six actual input reads, independently of all source amplitudes.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve.WindowTables
open ClassicalRoutines.Modular.NativePower
open QuantumFourierTransform.Semiclassical

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- One set of actual constants and both original signed row families. -/
structure Prepared (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (store : Store ctx) : Prop where
  constants : Outer.Preparation.Signed.Constants parameters.frame (actualCurveSpec I) store
  rows : Outer.Preparation.Signed.pairedRows (actualCurveSpec I) parameters.frame
    (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey store

private lemma constants_of_frame_input_reads {width : Nat}
    (frame : Outer.Frame ctx width) (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (before after : Store ctx)
    (words : ∀ {bits : Nat} (cell : CStorageRef ctx (.unsignedWord bits)),
      cell.key ∈ Driver.frameInputKeys frame →
      after.read (.storage cell) = before.read (.storage cell))
    (constants : Outer.Preparation.Signed.Constants frame curve before) :
    Outer.Preparation.Signed.Constants frame curve after := by
  exact Outer.Preparation.Signed.constants_of_word_reads frame curve before after
    (words frame.modulus.toCStorageRef
      (by simp only [Driver.frameInputKeys, List.mem_cons, true_or]))
    (words frame.zero.toCStorageRef
      (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true]))
    (words frame.one.toCStorageRef
      (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true]))
    (words frame.curveA.toCStorageRef
      (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true])) constants

private lemma prepared_of_reads (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (before after : Store ctx)
    (words : ∀ {width : Nat} (cell : CStorageRef ctx (.unsignedWord width)),
      cell.key ∈ Driver.frameInputKeys parameters.frame →
      after.read (.storage cell) = before.read (.storage cell))
    (x : after.read (.storage parameters.frame.x.toCStorageRef) =
      before.read (.storage parameters.frame.x.toCStorageRef))
    (y : after.read (.storage parameters.frame.y.toCStorageRef) =
      before.read (.storage parameters.frame.y.toCStorageRef))
    (prepared : Prepared parameters I before) : Prepared parameters I after := by
  refine ⟨constants_of_frame_input_reads parameters.frame (actualCurveSpec I)
    before after words prepared.constants, ?_⟩
  exact Outer.Preparation.Signed.pairedRows_of_array_reads parameters.frame (actualCurveSpec I)
      (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey before after x y prepared.rows

/-- The selected current driver's values follow from the same retained preparation. -/
lemma Prepared.driverInputValues (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (before : Store ctx)
    (prepared : Prepared parameters I before) (position : Fin 34) :
    Driver.driverInputValues parameters.frame (actualCurveSpec I)
      (chronologicalBasePoint I position)
      (Sampling.chronologicalIndex position).row before :=
  driverInputValues_of_paired_rows I parameters.frame before
    prepared.constants prepared.rows position

/-- The real zero reset retains the same constants and all thirty-four rows. -/
lemma prepared_reset_zero (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex) (before : Store ctx)
    (prepared : Prepared parameters I before) :
    Prepared parameters I
      (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) before).1 := by
  apply prepared_of_reads parameters I before _
  · intro width cell _
    apply Cleanup.Parameters.zeroRunRecord_read
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      Driver.write_shape_key_ne parameters.resetParameters.output cell
        (by intro impossible; cases impossible)
  · apply Cleanup.Parameters.zeroRunRecord_read
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      Driver.write_shape_key_ne parameters.resetParameters.output parameters.frame.x.toCStorageRef
        (by intro impossible; cases impossible)
  · apply Cleanup.Parameters.zeroRunRecord_read
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      Driver.write_shape_key_ne parameters.resetParameters.output parameters.frame.y.toCStorageRef
        (by intro impossible; cases impossible)
  · exact prepared

attribute [local irreducible] Driver.namedDriverInstrument
  Sampling.Locality.namedMeasuredMiddleInstrument

/-- Every actual point and Fourier outcome retains that same one preparation invariant. -/
lemma prepared_named_middle (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ (original : Store ctx × services.HiddenState)
      (outcome : point.1 × Bits (index.lowerWidth + 1)),
      Prepared parameters I original.1 →
      Prepared parameters I
        ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
          original outcome).1.1 := by
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  dsimp only
  intro original outcome prepared
  apply prepared_of_reads parameters I original.1 _
  · intro width cell member
    exact Sampling.Locality.namedMeasuredMiddle_frame_word_read parameters index environment
      cell member original outcome
  · exact Sampling.Locality.namedMeasuredMiddle_array_read parameters index environment
      parameters.frame.x.toCStorageRef original outcome
  · exact Sampling.Locality.namedMeasuredMiddle_array_read parameters index environment
      parameters.frame.y.toCStorageRef original outcome
  · exact prepared

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
