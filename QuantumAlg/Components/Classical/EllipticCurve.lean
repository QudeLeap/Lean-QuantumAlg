/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.EllipticCurve.Representation.Model
public import QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native.Semantics
public import QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native.Resources
public import QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Correctness
public import QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Resources
public import QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Correctness
public import QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Resources

/-!
# Native fixed-width elliptic-curve components

Canonical point representations, actual equality, complete addition and
scalar multiplication share the current circuit interpreter.
-/
