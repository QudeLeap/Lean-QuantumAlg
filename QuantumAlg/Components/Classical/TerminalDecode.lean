/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.TerminalDecode.Encoding
public import QuantumAlg.Components.Classical.TerminalDecode.Circuit
public import QuantumAlg.Components.Classical.TerminalDecode.Resources
public import QuantumAlg.Components.Classical.TerminalDecode.AppendSemantics
public import QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
public import QuantumAlg.Components.Classical.TerminalDecode.Retained
public import QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics

/-!
# Native fixed-width terminal decoding

The individual owners provide intrinsic bit representations, actual shift and
conditional-increment circuits, complete store and quantum-reference semantics,
native resources and the retained run with its full output manifest.
-/
