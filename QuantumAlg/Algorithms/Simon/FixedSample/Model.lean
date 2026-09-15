/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Simon.Model
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Core.Measure.Distribution
public import QuantumAlg.Util.Classical.GF2
public import Mathlib.Probability.ProbabilityMassFunction.Constructions


import all QuantumAlg.Algorithms.Simon.Model
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.Classical.GF2
import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# The original fixed-sample Simon contract

The supplied circuit fixes both its one-attempt Born law and its native
Hadamard and oracle coordinates. The source certificates constrain this
same law. No batch distribution or classical answer is supplied separately.
-/

namespace QuantumAlg.SimonsProblem

open Simon

noncomputable section

universe u


/-- Canonical physical placement of the two `n`-qubit Simon registers. -/
public def layout (n : ℕ) : QubitLayout (2 * n) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

/-- Terminally measure the first `n` logical qubits, which carry the recovered
bit vector at the registered post-sampling boundary. -/
def measurement (n : ℕ) : TerminalZMeasure (layout n) n :=
  zMeasureAt (layout n)
    (fun index => ⟨index.val, by omega⟩)
    (by
      intro left right h
      apply Fin.ext
      exact congrArg (fun value : Fin (2 * n) => value.val) h)

/-- Classical bit-vector output of the terminal Simon measurement. -/
public abbrev Outcome (n : ℕ) : Type :=
  Fin n → Bool

/-- Stable subroutine family for the Simon XOR-query stage. -/
def oracleLabel (n : ℕ) : QuantumAlg.Resource.SubroutineLabel where
  family := "simon"
  name := "simon-xor-oracle"
  parameters := [n]

/-! ### Canonical fixed-sample endpoint -/

namespace FixedSample

/-- Fixed-width unsigned word used by the executable reducer. -/
public abbrev Word (width : Nat) := ClassicalAlgorithms.Word width

/-- A fixed vector of sampled Simon equations. -/
abbrev Samples (rowCount width : Nat) :=
  ClassicalAlgorithms.GF2.Samples rowCount width

/-- Positive statistical slack.  The endpoint executes exactly `n + κ`
freshly prepared attempts and therefore exposes no zero-slack constructor. -/
public structure SecurityParameter where
  /-- Positive number of extra attempts beyond the register width. -/
  value : Nat
  positive : 0 < value

/-- Exact number of fresh Simon attempts. -/
def sampleCount (n : Nat) (κ : SecurityParameter) : Nat := n + κ.value

/-- Strict Hadamard coordinate used by the fixed sampling contract. -/
def hadamardEvent : Resource.Event .quantum :=
  .gate (.builtin "hadamard")

/-- Strict opaque Simon-oracle coordinate used by the fixed sampling contract. -/
def oracleEvent (n : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (oracleLabel n).quantum

/-- Implementation-independent circuit envelope for the two Hadamard layers
and one Simon XOR-oracle call. -/
public def circuitEventLimit (n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton hadamardEvent (2 * n) +
    ResourcePool.singleton (oracleEvent n)

/-- The endpoint starts every attempt from a sealed all-zero preparation. -/
def inputPreparation (n : Nat) : KnownPreparation (2 * n) :=
  KnownPreparation.zero (2 * n)

/-- Executable circuit descriptor and its fixed public sampling contract. -/
public structure SamplingCircuit (n : Nat) where
  /-- A nonempty measured register is required by terminal execution. -/
  widthPositive : 0 < n
  /-- Real Simon sampling circuit on the two `n`-qubit registers. -/
  circuit : UnitaryCircuit (Qubits (2 * n))
  /-- The circuit occupies the canonical two-register layout. -/
  circuitLayout : circuit.physical_idx = (layout n).systemIdx
  /-- The real circuit emits exactly the independent strict event limit. -/
  circuitEventCost : circuit.eventCost = circuitEventLimit n
  /-- The standard Hadamard/oracle/Hadamard circuit has unit depth at most 3. -/
  circuitUnitDepth :
    DepthExpr.depthEval (fun _event => 1) circuit.eventDepth ≤ 3

/-- The original normalized state after the supplied circuit acts on its fixed zero input. -/
def SamplingCircuit.evolvedState {n : Nat} (sampling : SamplingCircuit n) :
    QubitLayout.State (layout n) where
  state := PureState.ofNormalized
    (sampling.circuit.applyNormalized (inputPreparation n).normalized) (layout n).systemIdx
  system_idx_eq := rfl

/-- The source one-attempt Born law, with the original first-register readout. -/
public def SamplingCircuit.outcomePMF {n : Nat} (sampling : SamplingCircuit n) : PMF (Outcome n) :=
  (measurement n).outcomePMF sampling.evolvedState

/-- Decode one actually measured row by the same big-endian convention used
by the executable GF(2) reducer. -/
public def decodeWord {n : Nat} (outcome : Outcome n) : Word n :=
  ClassicalAlgorithms.TerminalDecode.eval { order := .bigEndian, bits := outcome }

/-- Source-facing certificates for the actual one-attempt Born distribution.

The source oracle has an arbitrary codomain `α`, so this layer cannot fabricate
a reversible encoding of `f`.  Instead `sampling` is the executable circuit,
and both semantic fields below refer directly to that circuit's sealed Born
PMF.  No batch, rank certificate, output PMF, or resource aggregate can be
supplied independently of `sampling`. -/
public structure Model {n : Nat} {α : Type u} (f : Simon.Oracle n α)
    (s : Simon.BitVec n) where
  /-- Executable circuit used for each independently prepared sample. -/
  sampling : SamplingCircuit n
  /-- Fixed-width representation of the source hidden mask. -/
  secret : Word n
  /-- Every machine coordinate represents the corresponding source `F₂` bit. -/
  secretRepresents :
    ∀ index, ClassicalAlgorithms.GF2.bitValue secret index = s index
  /-- Every supported result of the real prepared attempt is orthogonal to the
  represented hidden mask. -/
  orthogonalSupport : Simon.Promise f s →
    ∀ outcome ∈ sampling.outcomePMF.support,
      ClassicalAlgorithms.GF2.dot (decodeWord outcome) secret = 0
  /-- A wrong nonzero mask survives one real Simon equation with probability
  at most one half. -/
  wrongCandidateMass : Simon.Promise f s →
    ∀ candidate : Word n, candidate ≠ 0 → candidate ≠ secret →
      sampling.outcomePMF.toOuterMeasure
          {outcome |
            ClassicalAlgorithms.GF2.dot
              (decodeWord outcome) candidate = 0} ≤
        (2 : ENNReal)⁻¹

end FixedSample

end

end QuantumAlg.SimonsProblem
