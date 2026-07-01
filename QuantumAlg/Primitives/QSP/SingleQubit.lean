/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev
public import QuantumAlg.Primitives.QSP.SingleQubit.Fourier
public import QuantumAlg.Primitives.QSP.SingleQubit.Bridge
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis

/-!
# Single-qubit quantum signal processing

Single-qubit QSP interleaves a one-parameter signal rotation with tunable
processing phases.  This module re-exports the Chebyshev-basis, Fourier-basis,
bridge, and source phase-synthesis developments used by both standalone QSP
targets and multi-qubit QPP/QSVT lifts.
-/

@[expose] public section
