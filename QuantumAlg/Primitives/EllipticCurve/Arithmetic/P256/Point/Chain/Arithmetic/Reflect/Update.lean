/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Boundary
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Set

/-!
# Complete original target replacement of the actual retained-enable reflection

The original A readout and every complement bit identify the entire
output label. The actual reflection therefore changes only the original
numerical X word. Its canonical field interpretation is separate from
this exact total finite-word endpoint.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

namespace Reflect

noncomputable section

open EncodedBit EncodedBit.WindowLookup

attribute [local irreducible] layout WireSubsystem.complementWidth

/-- Complete original output equality, including arbitrary original pool and C/N/W values. -/
lemma step_eq_target_set (state : Frame.Raw) :
    step state =
      resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256)
        (Frame.work2 (step state)) state := by
  symm
  apply resultSetConstant_eq_of_readouts Frame.encoding_surjective
    (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256)
    (WordPort.bit_index_injective .work2)
  · intro index
    exact WordPort.bit_get .work2 index (step state)
  · intro observed outsideTarget
    by_cases selected : ∃ index : Fin 256, (WordPort.work1.bit index).wire = observed.wire
    · obtain ⟨index, same⟩ := selected
      rw [← eq_of_wire_eq (WordPort.work1.bit index) observed same,
        WordPort.bit_get, WordPort.bit_get]
      change (Frame.work1 (step state)).val.testBit index.val =
        (Frame.work1 state).val.testBit index.val
      rw [step_work1]
    · apply step_other observed ?_ state
      rintro ⟨index, same⟩
      obtain ⟨side, rfl⟩ :=
        (finSumFinEquiv : Fin 256 ⊕ Fin 256 ≃ Fin (256 + 256)).surjective index
      cases side with
      | inl position =>
          have location := wordPairSubsystem_left words.addend words.target
            words.addendDistinct words.targetDistinct words.separate position
          have found : (WordPort.work1.bit position.rev).wire = observed.wire :=
            location.symm.trans same
          exact selected ⟨position.rev, found⟩
      | inr position =>
          have location := wordPairSubsystem_right words.addend words.target
            words.addendDistinct words.targetDistinct words.separate position
          have found : (WordPort.work2.bit position.rev).wire = observed.wire :=
            location.symm.trans same
          exact outsideTarget position.rev found

/-- The actual placed reflection gives precisely this target replacement on its real clean A. -/
lemma program_apply_original (environment : OracleModel.empty.Interpretation) (state : Frame.Raw)
    (clean : Frame.work1 state = MAU.Addition.TTK.Reflection.zero 256) :
    program.applyNormalized environment (Native.ket state) =
      Native.ket (resultSetConstant
        (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256)
        (Frame.work2 (step state)) state) :=
  (program_apply_clean environment state clean).trans
    (congrArg Native.ket (step_eq_target_set state))

end

end Reflect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic
