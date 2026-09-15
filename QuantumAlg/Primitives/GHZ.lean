/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.GHZ.Construction
public import QuantumAlg.Primitives.GHZ.Endpoint

/-!
# Three-qubit GHZ construction and complete native execution

The exact mathematical construction and its complete native endpoint are
reusable primitives. The endpoint receives supplied owned zero input qubits
and explicitly retains all three physical output systems.
-/
