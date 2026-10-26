/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

/-!
# Actual measured-arithmetic allocation, loading and retained output run

All quantum systems are allocated and prepared in zero before native X
instructions load the canonical identity seed. Actual physical output and
reused vent cells are allocated once. The member executes its real measured
stage circuit on that same complete context [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The original control, auxiliary and three helper systems are zero; the source is one mod N. -/
def seedLabel (width N : Nat) : Physical.Registers width :=
  Physical.cleanLabel width false (BitVec.ofNat width (1 % N))

/-- Literal native X gates load the actual complete physical identity-seed label. -/
def sourceLoad (width N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (Physical.qubits width).toQuantum :=
  EncodedBit.Word.BasisLoad.program (Physical.qubits width) .empty (seedLabel width N)

lemma sourceLoad_zero {environment : OracleModel.empty.Interpretation} (width N : Nat) :
    (sourceLoad width N).applyNormalized environment
      (NormalizedVector.ket ((Physical.qubits width).basisEquiv.symm 0)) =
        NormalizedVector.ket ((Physical.qubits width).basisEquiv.symm (seedLabel width N)) :=
  EncodedBit.Word.BasisLoad.basisLoad_apply_zero (Physical.qubits width) .empty (seedLabel width N)

def load (N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  unitaryOfEqualWires (Physical.qubits width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (sourceLoad width N)

include noQuantum in
private lemma preparationDisjoint :
    List.Disjoint (Physical.qubits width).toQuantum.identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- Actual allocation and preparation supply all clean arithmetic promises internally. -/
def prepare (N : Nat) : Circuit model base (Context base noQuantum m ell width) :=
  (Circuit.prepareZero base base.canonicalFreshKey (Physical.qubits width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (preparationDisjoint base noQuantum width)).seq
    ((MeasurementCells.allocate (model := model) (bankContext base noQuantum width)
      2 (resultBits m ell + (width - 2))).seq
        (.unitary (load base noQuantum m ell width N)))

/-- The actual output reads only the retained exponent results, with all live storage preserved. -/
def resultRead :
    OutputRead (Context base noQuantum m ell width) (.fixedVector (resultBits m ell) (.finite 2)) :=
  .read (.fixedVector fun index =>
    .storage (resultCell base noQuantum m ell width index).toCStorageRef)

/-- The initialized actual run executes the measured member and retains its real output cells. -/
def run (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : (ZMod modulus.toNat)ˣ) :
    AlgorithmRun model base (Context base noQuantum m ell width)
      (.fixedVector (resultBits m ell) (.finite 2)) where
  code := (prepare base noQuantum m ell width modulus.toNat).seq
    (.embed (ContextEmbedding.identity (Context base noQuantum m ell width))
      (member base noQuantum m ell width wide modulus generator target))
  output := Output.all (Context base noQuantum m ell width)
    (resultRead base noQuantum m ell width)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
