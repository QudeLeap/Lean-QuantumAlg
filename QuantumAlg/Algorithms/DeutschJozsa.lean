/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.DeutschJozsa.Construction
public import QuantumAlg.Algorithms.DeutschJozsa.Endpoint
public import QuantumAlg.Algorithms.DeutschJozsa.Endpoint.Results

/-!
# Deutsch-Jozsa

The Construction module owns the original all-width promise and exact
oracle-circuit mathematics. The Endpoint module supplies the unique native
execution with actual preparation, intermediate Z writes, final classical
packing, and complete live Output.
-/
