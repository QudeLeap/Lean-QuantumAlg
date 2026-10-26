/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Frame
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference
import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Controlled.Placement

/-!
# Actual retained-enable reflection on the original point payload

The full physical placement consumes the generic two-word reflection.
The constant is the public fixed field modulus. The quantum target stays
in its original word and every other physical bit remains represented.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

namespace Reflect

noncomputable section

open EncodedBit GateSpec

attribute [local irreducible] WireSubsystem.complementWidth
attribute [local irreducible] layout
attribute [local irreducible] Frame.payloadWidth

def constant : Fin (2 ^ 256) := ⟨modulus, modulus_lt_capacity⟩

def program : Native.Circuit :=
  layout.place (MAU.Addition.TTK.Reflection.Controlled.program restEncoding 256 constant
    controlBit borrowedBit control_borrowed_ne)

def inputState (input : Word) (retained : Rest) : Frame.Raw :=
  layout.grouping.symm ((MAU.Addition.TTK.Reflection.zero 256, input), retained)

def outputWord (input : Word) (retained : Rest) : Word :=
  if controlBit.get retained then
    MAU.Addition.TTK.Reflection.reflected (width := 256) constant input else input

/-- Exact full-frame output restores A and retains all source metadata, pool and caller fields. -/
lemma program_apply (environment : OracleModel.empty.Interpretation) (input : Word)
    (retained : Rest) :
    program.applyNormalized environment (Native.ket (inputState input retained)) =
      Native.ket (inputState (outputWord input retained) retained) := by
  have placed := MAU.Addition.TTK.Reflection.Controlled.placed_program_apply_clean
    restEncoding 256 constant controlBit borrowedBit control_borrowed_ne layout
    environment input retained
  cases selected : controlBit.get retained <;>
    simpa only [program, inputState, outputWord, Native.ket, FullPlacement.targetLayout,
      selected, Bool.false_eq_true, ↓reduceIte] using placed

/-- The same actual placed word retains arbitrary input/reference coherence. -/
lemma program_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (input : Index → Word)
    (retained : Index → Rest) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator program environment Reference)
      (Native.referenceVector (fun index => inputState (input index) (retained index))
        reference amplitude) =
      Native.referenceVector
        (fun index => inputState (outputWord (input index) (retained index)) (retained index))
        reference amplitude :=
  Native.coherent_of_basis _ environment _ _
    (fun index => program_apply environment (input index) (retained index)) reference amplitude

end

end Reflect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic
