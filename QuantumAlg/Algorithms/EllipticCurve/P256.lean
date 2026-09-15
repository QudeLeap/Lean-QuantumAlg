/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources

/-!
# P-256 ECDLP same-run correctness and resources

This aggregate exposes the original certified P-256 domain and the public
`Algorithm.Solves` endpoint for one complete actual execution. Its 4,714 rounds
reuse the quantum bank through charged measurement and correction, run the
measured controlled point additions and Fourier readout, and check each
recovered scalar before retaining the first accepted result. The original
one-percent failure target and arbitrary external reference remain intact.

The same independent problem supplies the public quantum-space coordinates,
classical-memory ceilings, native-event bound and complete unit-depth bound.
The numerical ceilings are conservative allowances for this implementation.
-/
