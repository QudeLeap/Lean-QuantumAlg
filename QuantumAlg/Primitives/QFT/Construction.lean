/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Mathematics
public import QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
public import QuantumAlg.Primitives.QFT.Mathematics.BitReverse
public import QuantumAlg.Primitives.QFT.Source
public import QuantumAlg.Primitives.QFT.Source.FourierMatrix
public import QuantumAlg.Primitives.QFT.Source.Resources
public import QuantumAlg.Primitives.QFT.Source.Depth
public import QuantumAlg.Primitives.QFT.Lowering
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
# Native Fourier construction and verified standard-model lowering

The canonical source circuit uses native Hadamard, controlled-phase and SWAP
instructions. Algorithm consumers request a verified refinement into the
default native language. The inverse uses the generic adjoint transformation
of that actual refinement. Both levels retain exact matrices, literal event
counts, dependency depth, physical placements and spectator action.
-/
