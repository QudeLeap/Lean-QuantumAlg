/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base.Register
public import QuantumAlg.Core.Base.State
public import QuantumAlg.Core.Base.Gate
public import QuantumAlg.Core.Base.Tensor
public import QuantumAlg.Core.Base.Measurement

/-!
# QuantumAlg core base layer

This module re-exports the register-polymorphic state, operator, gate, tensor,
and measurement foundations consumed by `QuantumAlg.Core.Circuit` and named
components.
-/

@[expose] public section
