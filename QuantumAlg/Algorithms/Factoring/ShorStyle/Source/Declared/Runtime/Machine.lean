/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Geometry

/-!
# Concrete arbitrary-count declared Shor execution from its original caller

The actual code allocates and clears its own persistent classical heads,
prepares the single physical bank, executes the complete chronological loop,
then pays for one terminal optional-factor pack. The full original caller and
every actual retained source cell are present in the final output manifest.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
  (input : Input N) (count : Nat)

/-- The exact final live context of the actual initialized finite producer. -/
def context : RuntimeCtx .quantum :=
  Finite.context (Initialized.bank base noQuantum N) N count

/-- Genuine initialization feeds the actual complete finite tail and its sole paid pack. -/
def code : Circuit (executionModel N) base (context base noQuantum N count) :=
  (Initialized.ready base noQuantum N).seq
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count
      (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N))

/-- The actual terminal factor destination retains its original storage key. -/
def result : CWriteRef (context base noQuantum N count)
    (.option (.unsignedWord (modulusBits N))) :=
  Finite.liftWrite (Initialized.bank base noQuantum N) N count
    (Initialized.result base noQuantum N)

/-- Read the real packed factor while preserving the full live classical manifest. -/
def run : AlgorithmRun (executionModel N) base (context base noQuantum N count)
    (.option (.unsignedWord (modulusBits N))) where
  code := code base noQuantum N input count
  output := Output.all (context base noQuantum N count)
    (.read (.storage (result base noQuantum N count).toCStorageRef))

/-- The producer's final output lists every live original and retained source entry. -/
lemma output_listing :
    (run base noQuantum N input count).output.listing =
      (context base noQuantum N count).keys := rfl

/-- Every count retains precisely the same declared physical bank, without replacement. -/
lemma quantumWires :
    (context base noQuantum N count).quantumWires = (layout N).wires :=
  (Finite.quantumWires (Initialized.bank base noQuantum N) N count).trans
    (Initialized.bank_wires base noQuantum N)

/-- The concrete producer internally supplies every actual selector separation condition. -/
lemma separated :
    NativeFactorScan.Separated
      (Finite.cells (Initialized.bank base noQuantum N) N count
        (Initialized.cells base noQuantum N)) (result base noQuantum N count) :=
  Finite.separated (Initialized.bank base noQuantum N) N count
    (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
    (Initialized.separated base noQuantum N)

variable {environment : (executionModel N).Environment}

/-- Actual initialization, arbitrary complete repetition and final packing finish in zero. -/
lemma code_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History)) :
    BasisSeeded.Holds (context base noQuantum N count).quantumLayout.zeroLabel
      ((code base noQuantum N input count).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (Initialized.ready base noQuantum N)
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count
      (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)) _ state
    (Finite.code_seeded (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count
      (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
      ((Initialized.ready base noQuantum N).execute environment Reference state)
      (Initialized.ready_seeded base noQuantum N state))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
