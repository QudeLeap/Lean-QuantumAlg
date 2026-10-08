/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Mathematics
public import QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
public import QuantumAlg.Primitives.QFT.Mathematics.BitReverse
public import QuantumAlg.Primitives.QFT.Primitive
public import QuantumAlg.Primitives.QFT.Native
public import QuantumAlg.Primitives.QFT.Native.FourierMatrix
public import QuantumAlg.Primitives.QFT.Native.Resources
public import QuantumAlg.Primitives.QFT.Native.Depth
public import QuantumAlg.Primitives.QFT.Native.Macros
public import QuantumAlg.Primitives.QFT.Native.Inverse
public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
public import QuantumAlg.Primitives.QFT.Native.Inverse.Resources
public import QuantumAlg.Primitives.QFT.Native.Inverse.Depth

/-!
# Native quantum Fourier constructions

The forward circuit expands its Hadamard, controlled-phase and bit-reversal
steps into the default native language. The inverse uses the generic adjoint
transformation with explicit native inverse implementations. Exact Fourier
matrices, native resources, dependency depth and descriptive source macro
counts are proved in their respective construction owners.
-/
