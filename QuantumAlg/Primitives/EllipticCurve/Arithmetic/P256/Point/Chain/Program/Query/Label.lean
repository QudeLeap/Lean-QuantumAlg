/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate.Input
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Input

/-!
# Exact original initialized labels after each real query target update

The actual horizontal occurrences update Work2 and the vertical ones
update the numerator. Both identities preserve the entire original
initializer, including source padding, small history, C/N/W and address.
The binary-word law imposes no canonicality or active-sector condition.
These are descriptions of already established paid target effects.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open EncodedBit.WindowLookup Arithmetic.Call Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus clearedInitial

/-- The two original numerical inputs after replacing the actual occurrence's target. -/
def queryUpdated (occurrence : Fin 6) (x y updated : Fin (2 ^ modulus.size)) :
    Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size) :=
  if occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4 then
    (updated, y) else (x, updated)

/-- The real original setter returns exactly the full initializer with its one updated word. -/
lemma querySet_clearedInitial (occurrence : Fin 6)
    (x y updated : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    resultSetConstant (Window.resultWord (Window.QueryColumns.assignment occurrence).target)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) updated)
        (clearedInitial x y flags address) =
      clearedInitial (queryUpdated occurrence x y updated).1
        (queryUpdated occurrence x y updated).2 flags address := by
  by_cases horizontal : occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4
  · simpa only [queryUpdated, Window.QueryColumns.assignment, if_pos horizontal,
      Offset.Placed.horizontal] using
      clearedInitial_setWork2 x updated y flags address
  · simp only [queryUpdated, Window.QueryColumns.assignment, if_neg horizontal,
      Offset.Placed.vertical]
    rw [resultSetConstant_withNumerator]
    exact clearedInitial_withNumerator x y updated flags address

/-- Ordinary field coordinates retain the same full original initialized label. -/
lemma querySet_clearedInitial_residue (occurrence : Fin 6) (x y updated : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    resultSetConstant (Window.resultWord (Window.QueryColumns.assignment occurrence).target)
        (Residue.word updated)
        (clearedInitial (Residue.input x) (Residue.input y) flags address) =
      clearedInitial
        (queryUpdated occurrence (Residue.input x) (Residue.input y) (Residue.input updated)).1
        (queryUpdated occurrence (Residue.input x) (Residue.input y) (Residue.input updated)).2
        flags address := by
  have actual := querySet_clearedInitial occurrence (Residue.input x) (Residue.input y)
    (Residue.input updated) flags address
  rw [Residue.cast_input] at actual
  exact actual

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
