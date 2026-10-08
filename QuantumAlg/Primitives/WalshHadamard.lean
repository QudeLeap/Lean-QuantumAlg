/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Uniform
public import QuantumAlg.Primitives.WalshHadamard.Mathematics
public import QuantumAlg.Primitives.WalshHadamard.Pipeline
public import QuantumAlg.Primitives.WalshHadamard.Native
public import QuantumAlg.Primitives.WalshHadamard.Construction
public import QuantumAlg.Primitives.WalshHadamard.Construction.Matrix

/-!
# Native Walsh-Hadamard and Boolean phase-query constructions

The original normalized Walsh character matrix and phase-query states are
connected to an actual parallel Hadamard layer and one explicitly declared XOR
query. Construction owners provide their exact full matrices, native event
counts and unitary dependency depths. Preparation, stored Z measurements and
complete algorithm outputs belong to the runtime readout owners.
-/
