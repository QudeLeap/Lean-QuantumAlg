/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Context
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Storage
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Storage
import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete storage for the exact decoded order-finding sample

The original sample's quantum systems, separate finite measurement cells and
packed bits remain live. Decoding allocates one additional retained unsigned
word. Width zero uses the same context transformation and introduces no
sentinel quantum system or measurement.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

/-- The new result key is derived from all actually live sample keys. -/
def resultKey (t n : Nat) : StorageKey := (Sampling.post t n).canonicalFreshKey

theorem resultFresh (t n : Nat) : resultKey t n ∉ (Sampling.post t n).keys :=
  RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post t n)

/-- Read the packed bits written by the same original sampling execution. -/
def packedInput (t n : Nat) : CInputRef (Sampling.post t n) (.bits t) :=
  .storage (Sampling.resultRef t n).toCStorageRef

/-- Every sampled system and cell, together with the materialized unsigned result. -/
@[implicit_reducible] public def post (t n : Nat) : RuntimeCtx .quantum :=
  (Sampling.post t n).addRetained (resultKey t n) (.unsignedWord t) (resultFresh t n)

/-- The returned value is read from the actual newly allocated result cell. -/
def resultRef (t n : Nat) : CInputRef (post t n) (.unsignedWord t) :=
  ClassicalRoutines.TerminalDecode.resultRef
    (Sampling.post t n) t (resultKey t n) (resultFresh t n)

theorem post_keys (t n : Nat) :
    (post t n).keys = resultKey t n :: (Sampling.post t n).keys := rfl

/-- No sampled quantum system is removed or renamed by classical decoding. -/
theorem post_quantumWires (t n : Nat) :
    (post t n).quantumWires = (Sampling.post t n).quantumWires := rfl

theorem post_physicalIdx (t n : Nat) :
    (post t n).physicalIdx = (Sampling.post t n).physicalIdx := rfl

theorem post_register (t n : Nat) :
    (post t n).register = (Sampling.post t n).register := rfl

end

end QuantumAlg.OrderFinding.Exact
