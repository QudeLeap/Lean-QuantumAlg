/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Cleanup
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Cleanup
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Geometry
import all QuantumAlg.Core.Algorithm.Identity
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# Every positive actual Shor run has complete first and reused quantum cycles

The first complete cycle includes actual initialization and preparation.
Every further requested attempt is complete and physically admitted. The
sole certain classical pack ends the same original run. Reassociation changes
sequence parentheses alone, retaining all weighted states, actual paths,
native events, chronological depth and both live-space peaks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
  (input : Input N) (further : Nat)

private def positiveAssociation :
    Circuit.Reassociation
      (code base noQuantum N input (further + 1))
      ((Initialized.code base noQuantum N input).seq
        (Finite.code (Iteration.context (Initialized.bank base noQuantum N) N) N
          input
          ((Iteration.quantumWires (Initialized.bank base noQuantum N) N).trans
            (Initialized.bank_wires base noQuantum N)) further
          (Completion.cells (Initialized.bank base noQuantum N) N
            (Initialized.cells base noQuantum N))
          (Completion.liftWrite (Initialized.bank base noQuantum N) N
            (Initialized.result base noQuantum N)))) := by
  let ctx := Initialized.bank base noQuantum N
  let cells := Initialized.cells base noQuantum N
  let result := Initialized.result base noQuantum N
  let first := Completion.code ctx N input (Initialized.bank_wires base noQuantum N) cells result
  let rest := Finite.body (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans (Initialized.bank_wires base noQuantum N))
    (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) further
  let packed := Finite.pack ctx N (further + 1) cells result
  exact (Circuit.Reassociation.seq (.refl (Initialized.ready base noQuantum N))
    (.seqAssoc first rest packed)).trans
      (Circuit.Reassociation.seqAssoc (Initialized.ready base noQuantum N)
        first (rest.seq packed)).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
