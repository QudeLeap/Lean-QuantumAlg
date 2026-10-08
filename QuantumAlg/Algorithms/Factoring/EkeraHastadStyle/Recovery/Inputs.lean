/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Util.Combinatorics

/-!
# Actual retained inputs of native batch recovery

Recovery reads the complete sampler parameter and the sixteen chronological
terminal values already stored by the real quantum batch. Its unit, early
factor and pair operands are closed structural projections of those cells.
The full unordered-pair list has exactly 120 entries in the original order;
forming these references does not sample, copy or allocate any data.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery

open Execution

/-- Existing parameter and chronological result cells consumed by recovery. -/
structure Inputs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- The retained generator, early-factor flag and factor payload. -/
  parameter : CInputRef ctx (ParameterShape N)
  /-- All sixteen actual measured and packed terminal values. -/
  outcomes : CInputRef ctx (.fixedVector 16 (.bits (measurementBits N)))

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The unit word comes from the same real sampler parameter used by every quantum member. -/
def unitInput (inputs : Inputs ctx N) : CInputRef ctx (.unsignedWord (modulusBits N)) :=
  .first inputs.parameter

/-- The original sampler's early-factor flag is read after the completed quantum batch. -/
def earlyFlag (inputs : Inputs ctx N) : CInputRef ctx .bit :=
  .first (.second inputs.parameter)

/-- The early-factor payload remains the actual modulus-width retained word. -/
def earlyWord (inputs : Inputs ctx N) : CInputRef ctx (.unsignedWord (modulusBits N)) :=
  .second (.second inputs.parameter)

/-- One chronological terminal operand is a structural projection of the retained vector. -/
def terminalInput (inputs : Inputs ctx N) (index : Fin 16) :
    CInputRef ctx (.bits (measurementBits N)) :=
  .vectorGet inputs.outcomes index

/-- The original ordered list of every unordered terminal pair. -/
def terminalPairs (inputs : Inputs ctx N) :
    List (CInputRef ctx (.bits (measurementBits N)) ×
      CInputRef ctx (.bits (measurementBits N))) :=
  (List.ofFn (terminalInput inputs)).unorderedPairs

/-- All sixteen chronological input positions produce exactly 120 literal recovery pairs. -/
theorem nativeRecovery_terminalPairs_length (inputs : Inputs ctx N) :
    (terminalPairs inputs).length = 120 := by
  rw [terminalPairs, List.length_unorderedPairs, List.length_ofFn]
  norm_num [Nat.choose]

/-- An actual vector projection reads exactly the terminal value at its original position. -/
theorem nativeRecovery_terminal_read (inputs : Inputs ctx N) (store : Store ctx)
    (index : Fin 16) :
    store.read (terminalInput inputs index) = (store.read inputs.outcomes).get index := rfl

/-- Reading the literal pair references yields the unchanged pair order of actual stored values. -/
theorem nativeRecovery_terminalPairs_read (inputs : Inputs ctx N) (store : Store ctx) :
    (terminalPairs inputs).map (fun pair => (store.read pair.1, store.read pair.2)) =
      (List.ofFn (fun index => (store.read inputs.outcomes).get index)).unorderedPairs := by
  have pairs := List.unorderedPairs_map (List.ofFn (terminalInput inputs))
    (fun input : CInputRef ctx (.bits (measurementBits N)) => store.read input)
  have mapped : (List.ofFn (terminalInput inputs)).map
      (fun input : CInputRef ctx (.bits (measurementBits N)) => store.read input) =
        List.ofFn (fun index => (store.read inputs.outcomes).get index) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext index
    exact nativeRecovery_terminal_read inputs store index
  exact pairs.symm.trans (congrArg List.unorderedPairs mapped)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery
