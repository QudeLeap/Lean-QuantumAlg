/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.AlgorithmRun
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.Solves

/-!
# Complete quantum and classical algorithm API

The public interface exports typed circuits, mandatory all-live Output,
normalized inputs, independent Problem specifications, and the single-run
Algorithm wrapper. Solves requires actual success, state promises, complete
borrowed restoration, and explicit native resource limits on supported paths.
-/
