/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry

/-!
# Physical contexts for every finite EH batch count

The classical zero branch retains one optional result and the caller's bank.
Every positive branch uses the original EH bank and fixed retained store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The empty branch has one real retained optional result cell. -/
def zeroContext : RuntimeCtx .quantum :=
  base.addRetained base.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh

/-- Read the actual zero-branch optional factor cell. -/
def zeroRef : CWriteRef (zeroContext base N) (.option (.unsignedWord (modulusBits N))) :=
  .retainedHead base base.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh

/-- The finite result context contains no quantum bank at zero rounds. -/
public def context : Nat → RuntimeCtx .quantum
  | 0 => zeroContext base N
  | _ + 1 => Retry.context base noQuantum N

/-- The zero-count branch retains the caller's original physical wire list. -/
lemma zero_wires :
    (context base noQuantum N 0).quantumWires = base.quantumWires := rfl

/-- Every positive count has precisely the original-width EH bank. -/
lemma positive_wires (laterCount : Nat) :
    (context base noQuantum N (laterCount + 1)).quantumWires =
      (Native.layout N).wires :=
  Retry.context_wires base noQuantum N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
