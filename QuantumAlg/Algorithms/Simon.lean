/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Simon.Model
public import QuantumAlg.Algorithms.Simon.FixedSample.Model
public import QuantumAlg.Algorithms.Simon.FixedSample.Spec
public import QuantumAlg.Algorithms.Simon.FixedSample.Solves

/-!
# Fixed-sample Simon with actual bank reuse and retained recovery

The canonical endpoint executes exactly `n + κ` samples on one prepared
`2n`-qubit bank. Every later sample performs an actual paid reset; every
sample measures the first register and packs its row into a fixed slot.
The original executable GF(2) routine runs once on those same stored rows.

`QuantumAlg.SimonsProblem.main` proves the original success bound
`1 - 2⁻κ`, borrowed restoration, and independent native event, live-space
and unit-depth limits for the same complete execution. The hidden word and
source-model certificates are proof data; the algorithm takes only the
sampling circuit and positive slack. No expected stopping rule is asserted.

The source promise and one-sample Born contract retain the original scope
[dW19, qcnotes.tex:1407, 1409-1410]. All surviving bank wires, sample cells
and the optional result remain explicitly listed in the final output.
-/
