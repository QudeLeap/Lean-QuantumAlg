/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources

/-!
# Complete accumulation carrier and original control baseline

The existing source word supplies the selector, both borrowed bits and
every untouched coordinate. The target occupies the second word. The
three-pivot construction and control borrowing follow
[G17, paper.tex:276-293,319-334]. Both implementations share this exact carrier.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- Selector, untouched source coordinates, borrowed flag, target, borrowed helper. -/
abbrev CanonicalRegisters (extra : Nat) :=
  Bool × (Fin (2 ^ extra) × Addition.Gidney.Registers (extra + 3))

/-- Complete physical order of the selector, unused source bits, flag, target and helper. -/
def canonicalEncoding (extra : Nat) : BinaryLabelEncoding (CanonicalRegisters extra) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity extra)
      (Addition.Gidney.encoding (extra + 3)))

/-- The three source roles and all untouched coordinates retain their initial values. -/
def canonicalOutput {extra : Nat} (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) (state : CanonicalRegisters extra) :
    CanonicalRegisters extra :=
  (state.1, (state.2.1, (state.2.2.1,
    (if state.1 then modularWordOutput modulus constant state.2.2.2.1 else state.2.2.2.1,
      state.2.2.2.2))))

/-- The sole Boolean wire is its only physical position. -/
lemma singleBit_wire (position : Fin bool.width) : boolBit.wire = position := by
  apply Fin.ext
  have bound : position.val < 1 := position.isLt
  change 0 = position.val
  omega

/-- Physical bit lenses for the flag, target and arbitrary helper. -/
def offsetBits (width : Nat) : Fin (Addition.Gidney.encoding width).width →
    EncodedBit (Addition.Gidney.encoding width) :=
  productBit (fun _ => boolBit) (Addition.Gidney.oneDirtyBits width)

/-- The offset lenses cover their exact physical positions. -/
lemma offsetBits_wire (width : Nat)
    (position : Fin (Addition.Gidney.encoding width).width) :
    (offsetBits width position).wire = position := by
  exact productBit_wire (left := bool) (right := Addition.HRS.oneDirtyEncoding width)
    (fun _ => boolBit) (Addition.Gidney.oneDirtyBits width)
    singleBit_wire (Addition.Gidney.gidneyOneDirtyBits_wire width) position

/-- The unused source prefix beside the complete offset carrier. -/
abbrev bodyEncoding (extra : Nat) :=
  prod (finIdentity extra) (Addition.Gidney.encoding (extra + 3))

/-- Physical lenses for the untouched prefix and offset body. -/
def bodyBits (extra : Nat) : Fin (bodyEncoding extra).width →
    EncodedBit (bodyEncoding extra) :=
  productBit (finIdentityBit extra) (offsetBits (extra + 3))

/-- Each body lens retains its actual physical position. -/
lemma bodyBits_wire (extra : Nat) (position : Fin (bodyEncoding extra).width) :
    (bodyBits extra position).wire = position := by
  exact productBit_wire (left := finIdentity extra) (right := Addition.Gidney.encoding (extra + 3))
    (finIdentityBit extra) (offsetBits (extra + 3))
    (fun _ => rfl) (offsetBits_wire (extra + 3)) position

/-- The original offset list placed beside the untouched source prefix. -/
def bodyGates (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (bodyEncoding extra)) :=
  (Addition.Gidney.modularOffsetGates (extra + 3) modulus constant).map
    (GateSpec.prodRight (finIdentity extra))

/-- The existing two-word carrier supplies a temporary control-expansion wire. -/
lemma bodyCapacity (extra : Nat) : 5 ≤ bool.width + (bodyEncoding extra).width := by
  change 5 ≤ 1 + (extra + (1 + ((extra + 3) + 1)))
  omega

/-- Literal original full control, used only in exact comparison proofs. -/
def originalCanonicalGates (extra : Nat) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (canonicalEncoding extra)) :=
  controlRightList (fun _ => boolBit) (bodyBits extra)
    singleBit_wire (bodyBits_wire extra) (bodyCapacity extra) boolBit
    (bodyGates extra modulus constant)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
