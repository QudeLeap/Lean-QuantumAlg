/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.ResidueEncoding

/-!
# Short-DLP source register layout

The source register widths and faithful unit encoding are independent of the
oracle and circuit used to implement a short discrete logarithm query.
-/

namespace QuantumAlg.ShortDLP

noncomputable section

/-- Faithful computational-basis encoding of the multiplicative unit group.

The short-DLP probability argument only needs distinct group elements to
occupy distinct workspace basis states. It does not require those basis
labels to be canonical residue representatives. -/
public structure UnitEncoding (N n : Nat) where
  /-- Workspace basis label assigned to one unit. -/
  encode : (ZMod N)ˣ → Fin (2 ^ n)
  /-- Distinct units receive distinct workspace labels. -/
  encode_injective : Function.Injective encode

namespace UnitEncoding

/-- Canonical residue labels give the elementary unit encoding used by the
sealed-oracle implementation. -/
def ofResidueEncoding {N n : Nat} (encoding : BinaryResidueEncoding N n) :
    UnitEncoding N n where
  encode value := encoding.encode (value : ZMod N)
  encode_injective := by
    intro left right h
    apply Units.ext
    exact encoding.encode_injective h

instance {N n : Nat} :
    Coe (BinaryResidueEncoding N n) (UnitEncoding N n) :=
  ⟨ofResidueEncoding⟩

end UnitEncoding

/-- Public register dimensions for one short-DLP execution. -/
public structure RegisterParameters where
  /-- Upper bound on the short logarithm's bit length. -/
  m : Nat
  /-- Tradeoff register length. -/
  ell : Nat
  /-- Binary width of the encoded group workspace. -/
  workspaceBits : Nat

/-- First exponent-register width. -/
@[implicit_reducible]
def firstBits (params : RegisterParameters) : Nat :=
  params.ell + params.m

/-- Total number of qubits in the two exponent registers and workspace. -/
abbrev totalQubits (params : RegisterParameters) : Nat :=
  firstBits params + params.ell + params.workspaceBits

/-- Pack the three consecutive basis registers into the qubit basis. -/
def tripleIndex (params : RegisterParameters)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    Fin (2 ^ totalQubits params) :=
  prodEquiv (prodEquiv (a, b), workspace)

end

end QuantumAlg.ShortDLP
