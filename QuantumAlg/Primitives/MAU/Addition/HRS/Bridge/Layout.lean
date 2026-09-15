/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Bridge

/-!
# Shared physical layout of the HRS carry bridge

The physical fields are low word, high word, and one dirty output bit.
The widths may differ; no extra bit is inserted to equalize the halves.
This is the interface used for the borrowed-half recursion
[HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open BinaryLabelEncoding

/-- Exact shared low/high/dirty encoding. -/
def bridgeEncoding (low high : Nat) :
    BinaryLabelEncoding (BridgeRegisters (Fin (2 ^ low)) high) :=
  prod (prod (finIdentity low) (finIdentity high)) bool

theorem hrsBridgeEncoding_width (low high : Nat) :
    (bridgeEncoding low high).width = low + high + 1 := rfl

/-- A little-endian input bit of the low word. -/
def bridgeLowBit (low high : Nat) (bit : Fin low) : EncodedBit (bridgeEncoding low high) :=
  prodLeftBit (prod (finIdentity low) (finIdentity high)) bool
    (prodLeftBit (finIdentity low) (finIdentity high)
      (finIdentityBit low (WireAddress.littleEndianWire bit)))

/-- A little-endian target bit of the high word. -/
def bridgeHighBit (low high : Nat) (bit : Fin high) : EncodedBit (bridgeEncoding low high) :=
  prodLeftBit (prod (finIdentity low) (finIdentity high)) bool
    (prodRightBit (finIdentity low) (finIdentity high)
      (finIdentityBit high (WireAddress.littleEndianWire bit)))

/-- The sole external dirty bit. -/
def bridgeDirtyBit (low high : Nat) : EncodedBit (bridgeEncoding low high) :=
  prodRightBit (prod (finIdentity low) (finIdentity high)) bool boolBit

theorem hrsBridgeLowBit_get (low high : Nat) (bit : Fin low)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    (bridgeLowBit low high bit).get state = state.1.1.val.testBit bit.val := by
  change state.1.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

theorem hrsBridgeHighBit_get (low high : Nat) (bit : Fin high)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    (bridgeHighBit low high bit).get state = state.1.2.val.testBit bit.val := by
  change state.1.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

theorem hrsBridgeDirtyBit_get (low high : Nat)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    (bridgeDirtyBit low high).get state = state.2 := rfl

theorem hrsBridgeLowBit_wire (low high : Nat) (bit : Fin low) :
    (bridgeLowBit low high bit).wire.val = low - 1 - bit.val := rfl

theorem hrsBridgeHighBit_wire (low high : Nat) (bit : Fin high) :
    (bridgeHighBit low high bit).wire.val = low + (high - 1 - bit.val) := rfl

theorem hrsBridgeDirtyBit_wire (low high : Nat) :
    (bridgeDirtyBit low high).wire.val = low + high := rfl

theorem hrsBridgeLowHigh_disjoint (low high : Nat) (a : Fin low) (b : Fin high) :
    (bridgeLowBit low high a).wire ≠ (bridgeHighBit low high b).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [hrsBridgeLowBit_wire, hrsBridgeHighBit_wire] at hval
  omega

theorem hrsBridgeHighHigh_disjoint (low high : Nat) (a b : Fin high) (hne : a ≠ b) :
    (bridgeHighBit low high a).wire ≠ (bridgeHighBit low high b).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [hrsBridgeHighBit_wire, hrsBridgeHighBit_wire] at hval
  apply hne
  apply Fin.ext
  omega

theorem hrsBridgeHighDirty_disjoint (low high : Nat) (bit : Fin high) :
    (bridgeHighBit low high bit).wire ≠ (bridgeDirtyBit low high).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [hrsBridgeHighBit_wire, hrsBridgeDirtyBit_wire] at hval
  omega

end

end QuantumAlg.MAU.Addition.HRS
