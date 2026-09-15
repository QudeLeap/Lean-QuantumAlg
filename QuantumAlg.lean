/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util
public import QuantumAlg.Core
public import QuantumAlg.Components
public import QuantumAlg.Analysis
public import QuantumAlg.Primitives
public import QuantumAlg.Algorithms

/-!
# Lean-QuantumAlg

Formally verified quantum algorithms in Lean 4 on top of Mathlib.

This is the root module: it re-exports the public API of the library.

The public dependency direction is
`Util -> Core -> Components -> Analysis -> Primitives -> Algorithms`; imports may skip a
layer but never point backwards. `Components` is a top-level layer rather than
part of Core. Gate and Circuit cost and depth are derived quantities, and each
`QuantumAlgorithm` obtains output, resources, and depth from the same run.

- `QuantumAlg/Util/` — quantum-free, upstream-candidate helper lemmas
  (complex/exp identities, polynomial parity/reflection, `Fin (2^·)` index
  plumbing);
- `QuantumAlg/Core/` — state/gate/tensor/measurement framework;
- `QuantumAlg/Components/` — named kets, gates, oracles, and controls;
- `QuantumAlg/Analysis/` — quantum information and quantum learning theory;
- `QuantumAlg/Primitives/` — reusable lemmas (phase kickback,
  Hadamard/SWAP tests, QFT, ...);
- `QuantumAlg/Algorithms/` — end targets (Bell state, Deutsch-Jozsa, ...).
-/
