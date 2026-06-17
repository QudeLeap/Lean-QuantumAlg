/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Complex
public import QuantumAlg.Util.Polynomial
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Core.State
public import QuantumAlg.Core.Gate
public import QuantumAlg.Core.Tensor
public import QuantumAlg.Core.Measurement
public import QuantumAlg.Core.Cost
public import QuantumAlg.Core.Components.Kets
public import QuantumAlg.Core.Components.Gates
public import QuantumAlg.Core.Components.Oracle
public import QuantumAlg.Core.Components.Control
public import QuantumAlg.Primitives.BellPair
public import QuantumAlg.Primitives.WalshHadamard
public import QuantumAlg.Primitives.PhaseKickback
public import QuantumAlg.Primitives.HadamardTest
public import QuantumAlg.Primitives.SwapTest
public import QuantumAlg.Primitives.QFT
public import QuantumAlg.Primitives.QSP
public import QuantumAlg.Primitives.ControlledTransform
public import QuantumAlg.Primitives.LCU
public import QuantumAlg.Primitives.AmplitudeAmplification
public import QuantumAlg.Primitives.QuantumKernel
public import QuantumAlg.Algorithms.QPE
public import QuantumAlg.Algorithms.GHZ
public import QuantumAlg.Algorithms.SuperdenseCoding
public import QuantumAlg.Algorithms.Teleportation
public import QuantumAlg.Algorithms.DeutschJozsa
public import QuantumAlg.Algorithms.BernsteinVazirani
public import QuantumAlg.Algorithms.Simon
public import QuantumAlg.Algorithms.Grover
public import QuantumAlg.Algorithms.OrderFinding
public import QuantumAlg.Algorithms.AmplitudeEstimation

/-!
# Lean-QuantumAlg

Formally verified quantum algorithms in Lean 4 on top of Mathlib.

This is the root module: it re-exports the public API of the library.

- `QuantumAlg/Util/` — quantum-free, upstream-candidate helper lemmas
  (complex/exp identities, polynomial parity/reflection, `Fin (2^·)` index
  plumbing);
- `QuantumAlg/Core/` — state/gate/tensor/measurement framework, with named
  instances (kets, gates, oracle, control) under `Core/Components/`;
- `QuantumAlg/Primitives/` — reusable lemmas (phase kickback,
  Hadamard/SWAP tests, QFT, ...);
- `QuantumAlg/Algorithms/` — end targets (Bell state, Deutsch-Jozsa, ...).
  Trusted CSLib `TimeM` wrappers live beside the theorem endpoints they
  annotate; the shared adapter is `QuantumAlg.Core.Cost`.
-/

@[expose] public section
