/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.CopyValue
import all QuantumAlg.Components.Encoded.BitGates.Control
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest

/-!
# QuantumAlg.Components.EncodedBitGates

Public aggregate for encoded-bit gate primitives and word-level constructions.
-/
