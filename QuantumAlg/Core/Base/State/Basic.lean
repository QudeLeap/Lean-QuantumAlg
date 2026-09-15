/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Register
import all QuantumAlg.Core.Base.Register
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Raw Hilbert-space vectors over finite registers

`HilbertVector R` is the unrestricted complex Hilbert-space vector type.  Linear
combinations and intermediate vectors live here even when they are not normalized.
-/

section

namespace QuantumAlg

/-- Raw Hilbert-space vector for a finite quantum register. -/
public abbrev HilbertVector (R : Register) : Type := EuclideanSpace ℂ R.Index

end QuantumAlg

end
