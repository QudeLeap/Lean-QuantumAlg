/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Controlled
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

/-!
# Generic full-frame placement of the controlled clean-workspace reflection

The entire basis transport is proved at symbolic operand width and with
an arbitrary certified complete physical placement. Concrete consumers
instantiate this equation without normalizing their exponential basis.
-/

namespace QuantumAlg.MAU.Addition.TTK.Reflection.Controlled

noncomputable section

open EncodedBit GateSpec

variable {Rest Target : Type} (rest : BinaryLabelEncoding Rest)
    (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
    (different : control.wire ≠ work.wire)

lemma program_apply_clean (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ width)) (retained : Rest) :
    (program rest width constant control work different).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding rest width).encode ((Reflection.zero width, input), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding rest width).encode
          ((Reflection.zero width,
            if control.get retained then reflected constant input else input), retained))) := by
  have actual := (realizesList (QubitLayout.canonical _) .empty
    (gates rest width constant control work different) environment).apply_encoded_ket
      ((Reflection.zero width, input), retained)
  exact actual.trans (congrArg
    (fun state => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding rest width).encode state)))
    (gates_clean rest width constant input control work different retained))

/-- All original complementary coordinates remain represented by the same actual placement. -/
lemma placed_program_apply_clean {target : BinaryLabelEncoding Target}
    (placement : FullPlacement (encoding rest width) target)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ width)) (retained : Rest) :
    (placement.place (program rest width constant control work different)).applyNormalized
        environment (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          (target.encode (placement.grouping.symm ((Reflection.zero width, input), retained))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        (target.encode (placement.grouping.symm
          ((Reflection.zero width,
            if control.get retained then reflected constant input else input), retained)))) :=
  placement.place_ket_of_eq _ _ _
    (program_apply_clean rest width constant control work different environment input retained)

end

end QuantumAlg.MAU.Addition.TTK.Reflection.Controlled
