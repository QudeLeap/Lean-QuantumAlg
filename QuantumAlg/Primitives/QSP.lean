/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.SingleQubit
public import QuantumAlg.Primitives.QSP.MultiQubit

/-!
# Quantum signal processing

This is the umbrella module for single-qubit QSP characterizations and the
multi-qubit QSP descendants that lift those phase-synthesis results into
unitary polynomial and block-encoding transformations.

- `QuantumAlg.Primitives.QSP.SingleQubit` contains the Chebyshev/Fourier
  single-qubit signal forms and their bridge.
- `QuantumAlg.Primitives.QSP.MultiQubit` contains QPP and QSVT, whose public
  endpoints keep correctness and resource counts bound to one constructed
  circuit witness.
-/

@[expose] public section
