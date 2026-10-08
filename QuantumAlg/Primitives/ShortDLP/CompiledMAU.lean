/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ShortDLP.CompiledMAU.Family
public import QuantumAlg.Primitives.ShortDLP.CompiledMAU.GateCounts

/-!
# Actual modular arithmetic for the short-DLP group action

This declaration-free index collects the actual two selected-power gate
sequences, their exact source-state agreement, and independent native
resource contracts. The two exponent registers share one power word and
one auxiliary word of the exact public arithmetic width.
-/
