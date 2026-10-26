/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Prepared
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Components.Encoded.Circuit.Placement

/-!
# The actual fixed affine seed on every complete restart record

The same native loader maps the literal physical zero ket to the chosen
fixed X/Y values. Its complete complement stays zero. Transport follows
the original ordered physical wires and adds no gates. Combining this
proved action with the actual measured cleanup gives a complete restart
certificate, independent of the preceding input and measurement results.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialization

noncomputable section

open Execution

private def zeroPreimage {Data : Type} (labels : BinaryLabelEncoding Data)
    (onto : Function.Surjective labels.encode) : Data :=
  Classical.choose (onto ⟨0, Nat.two_pow_pos labels.width⟩)

private lemma zeroPreimage_encode {Data : Type} (labels : BinaryLabelEncoding Data)
    (onto : Function.Surjective labels.encode) :
    labels.encode (zeroPreimage labels onto) = ⟨0, Nat.two_pow_pos labels.width⟩ :=
  Classical.choose_spec (onto ⟨0, Nat.two_pow_pos labels.width⟩)

private def zeroRaw : Raw := zeroPreimage encoding encoding_surjective

private lemma zeroRaw_encode :
    encoding.encode zeroRaw = ⟨0, Nat.two_pow_pos encoding.width⟩ := by
  unfold zeroRaw
  exact zeroPreimage_encode encoding encoding_surjective

private lemma zeroRaw_bit (bit : EncodedBit encoding) : bit.get zeroRaw = false := by
  rw [← bit.get_eq, zeroRaw_encode]
  exact Nat.zero_testBit _

private lemma zeroRaw_coordinates : Frame.work2 zeroRaw.1 = 0 ∧
    Frame.numerator zeroRaw.1 = 0 := by
  constructor
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have actual := zeroRaw_bit (pointBit (Frame.work2Bit index))
    rw [pointBit_get, Frame.work2Bit_get] at actual
    exact actual.trans (Nat.zero_testBit index.val).symm
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have actual := zeroRaw_bit (pointBit (Frame.numeratorBit index))
    rw [pointBit_get, Frame.numeratorBit_get] at actual
    exact actual.trans (Nat.zero_testBit index.val).symm

/-- The one fixed full-bank seed actually prepared by the supplied fixed affine coordinates. -/
def seed (x y : Fin (2 ^ 256)) : Raw := step x y zeroRaw

lemma seed_coordinates (x y : Fin (2 ^ 256)) :
    Frame.work2 (seed x y).1 = x ∧ Frame.numerator (seed x y).1 = y :=
  step_coordinates x y zeroRaw zeroRaw_coordinates.1 zeroRaw_coordinates.2

/-- All original non-coordinate wires have their canonical zero values in the same seed. -/
lemma seed_other (x y : Fin (2 ^ 256)) (observed : EncodedBit encoding)
    (outsideX : ∀ index, ((resultWord .work2).bit index).wire ≠ observed.wire)
    (outsideY : ∀ index, ((resultWord .numerator).bit index).wire ≠ observed.wire) :
    observed.get (seed x y) = false :=
  (step_other x y zeroRaw observed outsideX outsideY).trans (zeroRaw_bit observed)

private lemma zero_basis :
    (QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode zeroRaw) =
      fun _ => 0 := by
  funext index
  change (BinaryBasis.bigEndianEquiv encoding.width).symm (encoding.encode zeroRaw) index = 0
  rw [zeroRaw_encode, BinaryBasis.bigEndianEquiv_symm_value]
  change finTwoEquiv.symm ((0 : Nat).testBit index.rev.val) = 0
  rw [Nat.zero_testBit]
  rfl

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx)

/-- This is only the original full physical-wire correspondence, with no additional instruction. -/
def physicalSeed (x y : Fin (2 ^ 256)) : ctx.quantumLayout.Basis :=
  basisOfEqualWires (QubitLayout.canonical encoding.width).toQuantum ctx.quantumLayout
    parameters.sameWires
      ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode (seed x y)))

def placedProgram (x y : Fin (2 ^ 256)) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires (QubitLayout.canonical encoding.width).toQuantum ctx.quantumLayout
    parameters.sameWires (program x y)

private lemma placed_zero :
    basisOfEqualWires (QubitLayout.canonical encoding.width).toQuantum ctx.quantumLayout
      parameters.sameWires
      ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode zeroRaw)) =
        parameters.zeroLabel := by
  funext wire
  obtain ⟨original, rfl⟩ := (positionsOfEqualWires
    (QubitLayout.canonical encoding.width).toQuantum ctx.quantumLayout
      parameters.sameWires).surjective wire
  apply Fin.ext
  have actual := basisOfEqualWires_value (QubitLayout.canonical encoding.width).toQuantum
    ctx.quantumLayout parameters.sameWires
      ((QubitLayout.canonical encoding.width).basisEquiv.symm (encoding.encode zeroRaw)) original
  exact actual.trans (congrArg Fin.val (congrFun zero_basis original))

/-- Full native semantics discharge the fixed-ket premise of physical re-preparation. -/
lemma placedProgram_zero (x y : Fin (2 ^ 256)) (environment : OracleModel.empty.Interpretation) :
    ((placedProgram parameters x y).matrix environment).apply
        (NormalizedVector.ket parameters.zeroLabel) =
      NormalizedVector.ket (physicalSeed parameters x y) := by
  have transported := UnitaryCircuit.Realizes.equalWires_apply_encoded_ket
    ctx.quantumLayout parameters.sameWires (program_realizes x y environment) zeroRaw
  have complete :
      ((placedProgram parameters x y).matrix environment).applyVec
        (NormalizedVector.ket parameters.zeroLabel).vec =
          (NormalizedVector.ket (physicalSeed parameters x y)).vec := by
    rw [placedProgram, ← placed_zero parameters]
    simpa only [physicalSeed, seed] using transported
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun vector => vector index) complete

/-- Actual all-record cleanup and the actual native affine loader restore the same fixed seed. -/
lemma restartCleanup (x y : Fin (2 ^ 256))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup
      (parameters.prepared (placedProgram parameters x y)) environment :=
  parameters.prepared_restartCleanup environment (placedProgram parameters x y)
    (physicalSeed parameters x y) (placedProgram_zero parameters x y environment.quantum) noBorrowed

end

end Initialization

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
