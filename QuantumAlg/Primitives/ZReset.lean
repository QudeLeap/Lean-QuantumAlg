/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Circuit
public import QuantumAlg.Primitives.ZReset.Semantics
public import QuantumAlg.Primitives.ZReset.Resources
public import QuantumAlg.Primitives.ZReset.Reference
public import QuantumAlg.Primitives.ZReset.Endpoint

/-!
# Z measurement followed by correction selected from classical storage

The primitive and its complete owned-system endpoint use the single circuit
interpreter on arbitrary joint quantum-reference inputs. Their Output retains
the measured system and its actual finite classical result.
-/
