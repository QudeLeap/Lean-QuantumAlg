/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Construction
public import QuantumAlg.Primitives.QFT.Endpoint
public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint

/-!
# Quantum Fourier transform

The construction owner proves the exact all-width Fourier operator and its
native gate counts. The endpoint owner supplies its complete typed execution
with an owned input register and an explicit live-storage output manifest.
The semiclassical endpoint proves the complete adaptive measured instrument
with its actual retained output bits and arbitrary external references.
-/
