/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.EllipticCurve.PointAddition
public import QuantumAlg.Primitives.EllipticCurve.Resource
public import QuantumAlg.Primitives.EllipticCurve.CleanComposition
public import QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication
public import QuantumAlg.Primitives.EllipticCurve.ScalarMultiplicationEndpoint
public import QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.StructuredCircuit

/-!
# Elliptic-curve primitives

This module re-exports elliptic-curve circuit-facing primitive components,
including encoded structured-circuit witness layers.
-/

@[expose] public section
