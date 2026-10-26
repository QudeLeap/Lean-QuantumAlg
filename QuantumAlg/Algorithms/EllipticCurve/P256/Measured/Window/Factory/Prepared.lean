/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Inputs
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prepared
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Specification

/-!
# The actual current factory reads supply the existing preparation invariant

The recovery read condition on the actual Store after the persistent and
fresh-feedback transports supplies the four constants and both signed row
families of the preparation invariant.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables

private lemma signed_post_of_readConditions {outer inner : RuntimeCtx .quantum}
    (original : Sampling.Storage.Inputs outer) (lift : Transport outer inner)
    (first second : AffinePoint original.curve.curve) (store : Store inner)
    (conditions : Sampling.Storage.Conditional.readConditions original
      first.toMathlib second.toMathlib (fun input => store.read (lift.liftInput input))) :
    Outer.Preparation.Signed.Constants (original.frame.transport lift) original.curve store ∧
      Outer.Preparation.Signed.pairedRows original.curve (original.frame.transport lift)
        first second store := by
  rcases conditions with ⟨_, modulus, zero, one, curveA, rows⟩
  have constants : Outer.Preparation.Signed.Constants
      (original.frame.transport lift) original.curve store := by
    constructor
    · simpa only [Outer.Frame.transport, ClassicalRoutines.Modular.NativePower.wordRead,
        Transport.liftWrite_input] using modulus
    · simpa only [Outer.Frame.transport, Transport.liftWrite_input] using zero
    · simpa only [Outer.Frame.transport, Transport.liftWrite_input] using one
    · simpa only [Outer.Frame.transport, Transport.liftWrite_input] using curveA
  refine ⟨constants, ?_⟩
  have readRow (array : CWriteRef outer (.fixedVector 34 (.unsignedWord 256)))
      (index : Fin 34) :
      store.read (rowRead (lift.liftWrite array) index) =
        (store.read (lift.liftInput (.storage array.toCStorageRef))).get index :=
    Sampling.Storage.Conditional.actual_row_read lift array store index
  apply (Outer.Preparation.Signed.pairedRows_iff original.curve
    (original.frame.transport lift) first second store).2
  constructor
  · intro index
    simp only [Outer.Frame.coordinates, Outer.Frame.transport]
    rw [readRow, readRow]
    exact rows.1 index
  · intro index
    simp only [Outer.Frame.coordinates, Outer.Frame.transport]
    rw [readRow, readRow]
    exact rows.2 index

/-- The original reads supply preparation for the actual retained and fresh-feedback sampler. -/
lemma current_sampler_prepared_of_readConditions {outer inner : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      outer.quantumLayout.wires)
    (results : Fourier.Results outer) (frame : Outer.Frame outer 256)
    (base target : CInputRef outer (PointShape 256))
    (next : Transport
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (nextWires :
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx
        outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch next) (store : Store inner) :
    let original := inputs I sameWires results frame base target
    let lift := (Sampling.Recovery.persistentTransport outer).compose next
    Sampling.Storage.Conditional.readConditions original
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
        (fun input => store.read (lift.liftInput input)) →
      let retained := original.transport
        (Sampling.Recovery.persistentTransport outer) (Sampling.Recovery.persistent_wires outer)
      Good.Prepared (retained.samplerParameters next nextWires scratch fresh) I store := by
  dsimp only
  intro conditions
  have post := signed_post_of_readConditions
    (inputs I sameWires results frame base target)
    ((Sampling.Recovery.persistentTransport outer).compose next)
    (DomainParameters.basePoint I.curveCert I.baseCert) I.publicKey store conditions
  exact ⟨post.1, post.2⟩

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
