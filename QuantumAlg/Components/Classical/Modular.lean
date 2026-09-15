/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Modular.Encoding
public import QuantumAlg.Components.Classical.Modular.Reduce.Native.Semantics
public import QuantumAlg.Components.Classical.Modular.Reduce.Native.Resources
public import QuantumAlg.Components.Classical.Modular.NativePower.Correctness
public import QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
public import QuantumAlg.Components.Classical.Modular.NativePower.Full.Space

/-!
# Native fixed-width modular arithmetic

Canonical residue encodings, actual quotient/remainder reduction, and scoped
modular exponentiation with their complete state and resource contracts.
-/
