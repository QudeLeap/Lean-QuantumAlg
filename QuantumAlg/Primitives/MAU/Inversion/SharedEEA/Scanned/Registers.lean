/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Util.NumberTheory.SharedEEA.ScanMetadata

/-!
# Complete physical frame of a scanned shared-EEA microstep

All original payload, finite metadata, phase and control fields remain live.
The appended pool has one full-carry address word, an equally wide unary
prefix word and a conjunction bit. P-256 therefore adds 21 actual systems;
their preparation, use and restoration belong to the circuit consumers.
The original fields follow [LYL+26, sec_EEA/sub_regshare.tex:16-26]. The pool
and its exact metadata capacity are project derivations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned

noncomputable section

open EncodedBit BinaryLabelEncoding NumberTheory.SharedEEA

/-- Address and prefix word are separate, followed by one actual conjunction bit. -/
abbrev Pool (width : Nat) :=
  BitVec (ScanMetadata.addressWidth width) × (BitVec (ScanMetadata.addressWidth width) × Bool)

/-- Keep every original source field beside the complete scan workspace. -/
abbrev Data (width : Nat) := Registers width × Pool width

/-- The pool uses the literal binary encoding of all its finite labels. -/
def poolEncoding (width : Nat) : BinaryLabelEncoding (Pool width) :=
  .prod (wordEncoding (ScanMetadata.addressWidth width))
    (.prod (wordEncoding (ScanMetadata.addressWidth width)) .bool)

/-- Original wires precede the actual address, prefix and conjunction wires. -/
def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  .prod (SharedEEA.encoding width) (poolEncoding width)

/-- Exact space of the new pool, without reclassifying any original source wire. -/
lemma poolEncoding_width (width : Nat) :
    (poolEncoding width).width = ScanMetadata.poolWidth width := by
  change ScanMetadata.addressWidth width + (ScanMetadata.addressWidth width + 1) =
    2 * ScanMetadata.addressWidth width + 1
  omega

/-- All original systems and all pool systems remain physically resident together. -/
lemma encoding_width (width : Nat) :
    (encoding width).width = 2 * (width + 3) + 4 * width.size + 5 +
      ScanMetadata.poolWidth width := by
  change (SharedEEA.encoding width).width + (poolEncoding width).width = _
  rw [SharedEEA.encoding_width, poolEncoding_width]

/-- Lift one existing source coordinate without changing its physical location. -/
def sourceBit (width : Nat) (bit : EncodedBit (SharedEEA.encoding width)) :
    EncodedBit (encoding width) :=
  prodLeftBit (SharedEEA.encoding width) (poolEncoding width) bit

/-- A physical big-endian address coordinate, including the high carry bit. -/
def addressBit (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    EncodedBit (encoding width) :=
  prodRightBit (SharedEEA.encoding width) (poolEncoding width)
    (prodLeftBit (wordEncoding (ScanMetadata.addressWidth width))
      (.prod (wordEncoding (ScanMetadata.addressWidth width)) .bool) (wordBit index))

/-- A physical big-endian prefix coordinate, disjoint from every address and source bit. -/
def prefixBit (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    EncodedBit (encoding width) :=
  prodRightBit (SharedEEA.encoding width) (poolEncoding width)
    (prodRightBit (wordEncoding (ScanMetadata.addressWidth width))
      (.prod (wordEncoding (ScanMetadata.addressWidth width)) .bool)
      (prodLeftBit (wordEncoding (ScanMetadata.addressWidth width)) .bool (wordBit index)))

/-- The final pool bit combines controls before the selected payload operation. -/
def conjunctionBit (width : Nat) : EncodedBit (encoding width) :=
  prodRightBit (SharedEEA.encoding width) (poolEncoding width)
    (prodRightBit (wordEncoding (ScanMetadata.addressWidth width))
      (.prod (wordEncoding (ScanMetadata.addressWidth width)) .bool)
      (prodRightBit (wordEncoding (ScanMetadata.addressWidth width)) .bool boolBit))

/-- Original source reads retain all original fields and ignore only the new pool. -/
lemma sourceBit_get (width : Nat) (bit : EncodedBit (SharedEEA.encoding width))
    (state : Data width) : (sourceBit width bit).get state = bit.get state.1 := by rfl

/-- Address bits read the actual appended finite word. -/
lemma addressBit_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width))
    (state : Data width) :
    (addressBit width index).get state = state.2.1.getMsbD index.val :=
  wordBit_get index state.2.1

/-- Prefix bits read their own word, even before initialization. -/
lemma prefixBit_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width))
    (state : Data width) :
    (prefixBit width index).get state = state.2.2.1.getMsbD index.val :=
  wordBit_get index state.2.2.1

/-- The conjunction bit is an independent physical state coordinate. -/
lemma conjunctionBit_get (width : Nat) (state : Data width) :
    (conjunctionBit width).get state = state.2.2.2 := by rfl

/-- The complete P-256 inversion frame is 559 original systems plus the 21-bit pool. -/
lemma p256_encoding_width : (encoding 256).width = 580 := by
  rw [encoding_width, ScanMetadata.p256_poolWidth]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned
