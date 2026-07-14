/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util
public import QuantumAlg.Core
public import QuantumAlg.Core.Components
public import QuantumAlg.Primitives
public import QuantumAlg.Primitives.QNN.Expressivity
public import QuantumAlg.Algorithms

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
