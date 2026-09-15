/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
public import QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.Nat.FixedWidth
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation

/-!
# Fixed-layout VBE modular exponentiation

The physical construction is the elementary square-and-multiply route from
Vedral--Barenco--Ekert [VBE95, 9511018.tex:372-416].  One fixed register stores
the complete exponent word, the actual VBE modular-multiplication workspace,
and one clean control-decomposition bit.  At exponent position `i`, the real
VBE multiplication program for `u^(2^i)` is lifted into the shared layout and
mechanically controlled by exponent wire `i`.

The input value never selects a program or gate list.  Correctness, the clean
normalized endpoint, strict event cost, symbolic and evaluated event depth,
per-event query depth, and gate counts all come from the same folded actual
`UnitaryCircuit`.
-/

section

namespace QuantumAlg
namespace MAU.Exponentiation

open QuantumAlg.Nat.FixedWidth.UnitExponentiation

noncomputable section

/-! ### Semantic accumulator action -/

/-- High-level modular-exponentiation accumulator data. -/
structure Data (m N : Nat) where
  /-- Complete `m`-bit exponent. -/
  exponent : Fin (2 ^ m)
  /-- Residue multiplied by the selected power of the base unit. -/
  target : ZMod N
deriving DecidableEq

namespace Data

/-- Two semantic accumulator values are equal when both named fields agree. -/
@[ext] theorem ext {m N : Nat} {x y : Data m N}
    (hexponent : x.exponent = y.exponent)
    (htarget : x.target = y.target) : x = y := by
  cases x
  cases y
  simp_all

/-- Apply the multiplicative-accumulator action `target ↦ u^exponent * target`. -/
def applyUnit {m N : Nat} (u : (ZMod N)ˣ) (x : Data m N) : Data m N where
  exponent := x.exponent
  target := ((u ^ x.exponent.val : (ZMod N)ˣ) : ZMod N) * x.target

@[simp] theorem applyUnit_exponent {m N : Nat}
    (u : (ZMod N)ˣ) (x : Data m N) :
    (x.applyUnit u).exponent = x.exponent :=
  rfl

@[simp] theorem applyUnit_target {m N : Nat}
    (u : (ZMod N)ˣ) (x : Data m N) :
    (x.applyUnit u).target =
      ((u ^ x.exponent.val : (ZMod N)ˣ) : ZMod N) * x.target :=
  rfl

end Data

/-! ### One fixed physical layout -/

namespace VBECircuit

/-- The actual VBE multiplication register reused at every exponent bit. -/
abbrev MultiplicationRegisters (n : Nat) :=
  MAU.Multiplication.VBECircuit.Registers n

/-- Fixed exponentiation layout: exponent, VBE multiplication workspace, and
one clean bit used by the gate-level control decomposition. -/
structure Registers (m n : Nat) where
  /-- Complete exponent word. -/
  exponent : Fin (2 ^ m)
  /-- Shared VBE multiplication workspace. -/
  multiplication : MultiplicationRegisters n
  /-- Clean work bit reused by every mechanically controlled base gate. -/
  controlWork : Bool
deriving DecidableEq

/-- Product representation used by the binary encoding. -/
abbrev RawRegisters (m n : Nat) :=
  Fin (2 ^ m) × (MultiplicationRegisters n × Bool)

/-- Equivalence between the named layout and its nested product representation. -/
def registersEquiv (m n : Nat) : Registers m n ≃ RawRegisters m n where
  toFun := fun x => (x.exponent, (x.multiplication, x.controlWork))
  invFun := fun x =>
    { exponent := x.1
      multiplication := x.2.1
      controlWork := x.2.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rcases x with ⟨exponent, multiplication, controlWork⟩
    rfl

/-- Nested product encoding before relabeling to `Registers`. -/
def rawEncoding (m n : Nat) : BinaryLabelEncoding (RawRegisters m n) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.finIdentity m)
    (BinaryLabelEncoding.prod
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool)

/-- Fixed binary encoding of the complete exponentiation layout.  The concrete
multiply-swap-inverse-multiply register discipline is corroborated by
Beauregard's controlled multiplier construction; the exact width below belongs
to this fixed VBE implementation [Bea02, arxivfact.tex:129-146]. -/
def encoding (m n : Nat) : BinaryLabelEncoding (Registers m n) :=
  (rawEncoding m n).relabel (registersEquiv m n)

/-- Named-register relabeling preserves the actual circuit carrier width. -/
@[simp] theorem encoding_width_eq_rawEncoding_width (m n : Nat) :
    (encoding m n).width = (rawEncoding m n).width := by
  rfl

/-- Width of the fixed layout: `m` exponent qubits, the `5*n+4` VBE
multiplication layout, and one clean control-work qubit. -/
theorem encoding_width (m n : Nat) :
    (encoding m n).width = m + (5 * n + 4 + 1) := by
  simp [encoding, rawEncoding]

/-- Complete computational-basis label type of the fixed layout. -/
abbrev Label (m n : Nat) := Fin (2 ^ (encoding m n).width)

/-- Embed semantic accumulator data into the clean physical VBE workspace. -/
def cleanRegisters (m n N : Nat) (x : Data m N) : Registers m n where
  exponent := x.exponent
  multiplication :=
    MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding n N
      (MAU.Multiplication.cleanInput x.target)
  controlWork := false

/-- One exponent bit before the named-register relabeling. -/
def rawExponentBit (m n : Nat) (bit : Fin m) :
    EncodedBit (rawEncoding m n) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.finIdentity m)
    (BinaryLabelEncoding.prod
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.finIdentityBit m
      (WireAddress.littleEndianWire bit))

/-- One exponent bit in the complete fixed layout. -/
def exponentBit (m n : Nat) (bit : Fin m) : EncodedBit (encoding m n) :=
  (rawExponentBit m n bit).relabel (registersEquiv m n)

/-- The clean control-decomposition work bit before named-register relabeling. -/
def rawControlWorkBit (m n : Nat) : EncodedBit (rawEncoding m n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m)
    (BinaryLabelEncoding.prod
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

/-- The clean control-decomposition work bit in the complete layout. -/
def controlWorkBit (m n : Nat) : EncodedBit (encoding m n) :=
  (rawControlWorkBit m n).relabel (registersEquiv m n)

@[simp] theorem rawExponentBit_get (m n : Nat) (bit : Fin m)
    (x : RawRegisters m n) :
    (rawExponentBit m n bit).get x = x.1.val.testBit bit.val := by
  change x.1.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

@[simp] theorem rawControlWorkBit_get (m n : Nat)
    (x : RawRegisters m n) :
    (rawControlWorkBit m n).get x = x.2.2 := by
  rfl

@[simp] theorem exponentBit_get (m n : Nat) (bit : Fin m)
    (x : Registers m n) :
    (exponentBit m n bit).get x = x.exponent.val.testBit bit.val := by
  change x.exponent.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val =
    x.exponent.val.testBit bit.val
  rw [WireAddress.bitIndex_littleEndianWire]

@[simp] theorem controlWorkBit_get (m n : Nat) (x : Registers m n) :
    (controlWorkBit m n).get x = x.controlWork := by
  rfl

/-! ### One actual controlled multiplication stage -/

/-- High-level effect of one controlled-power stage. -/
def stageAction {m N : Nat} (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Data m N) : Data m N where
  exponent := x.exponent
  target := (selectedUnit u x.exponent.val bit : ZMod N) * x.target

/-- Unconditional multiplication by the static unit assigned to `bit`. -/
def multiplicationAction {m N : Nat} (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Data m N) : Data m N where
  exponent := x.exponent
  target := (stageUnit u bit : ZMod N) * x.target

/-- Lift the exact VBE multiplication gate list into the middle register while
leaving the exponent and clean control-work bit untouched. -/
def liftedMultiplicationGates (m n N : Nat) (u : (ZMod N)ˣ)
    (bit : Fin m) :
    List (EncodedBit.GateSpec (rawEncoding m n)) :=
  ((MAU.Multiplication.VBECircuit.multiplicationGates
      n N (stageUnit u bit)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight
      (BinaryLabelEncoding.finIdentity m))

/-- The lifted actual multiplication program is compiled directly from the
lifted primitive list. -/
def liftedMultiplicationProgram (m n N : Nat) (u : (ZMod N)ˣ)
    (bit : Fin m) : UnitaryCircuit (Qubits (rawEncoding m n).width) :=
  EncodedBit.GateSpec.programList
    (liftedMultiplicationGates m n N u bit)

/-- The lifted gate list acts on the multiplication workspace and preserves
the exponent and clean-work fields. -/
theorem liftedMultiplicationGates_stepList
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (x : RawRegisters m n) :
    EncodedBit.GateSpec.stepList
        (liftedMultiplicationGates m n N u bit) x =
      (x.1,
        (MAU.Multiplication.VBECircuit.multiplicationStep
          n N (stageUnit u bit) x.2.1,
        x.2.2)) := by
  change
    EncodedBit.GateSpec.stepList
        (((MAU.Multiplication.VBECircuit.multiplicationGates
            n N (stageUnit u bit)).map
          (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          (EncodedBit.GateSpec.prodRight
            (BinaryLabelEncoding.finIdentity m))) x = _
  rw [
    EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodLeft]
  rfl

/-- Full-register semantic action of the lifted, uncontrolled multiplication. -/
def liftedMultiplicationStep (m n N : Nat) (u : (ZMod N)ˣ)
    (bit : Fin m) (x : Registers m n) : Registers m n where
  exponent := x.exponent
  multiplication :=
    MAU.Multiplication.VBECircuit.multiplicationStep
      n N (stageUnit u bit) x.multiplication
  controlWork := x.controlWork

/-- Relabeling the lifted gate-list fold gives the named-register
multiplication step. -/
theorem liftedMultiplicationStep_eq_gateList
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Registers m n) :
    (registersEquiv m n).symm
        (EncodedBit.GateSpec.stepList
          (liftedMultiplicationGates m n N u bit)
          (registersEquiv m n x)) =
      liftedMultiplicationStep m n N u bit x := by
  rw [liftedMultiplicationGates_stepList]
  cases x
  rfl

/-- The lifted actual circuit realizes its full-register semantic action. -/
theorem liftedMultiplication_realizes
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit.Realizes (encoding m n)
      (liftedMultiplicationProgram m n N u bit)
      (liftedMultiplicationStep m n N u bit) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.relabel (registersEquiv m n)
      (EncodedBit.GateSpec.realizesList
        (liftedMultiplicationGates m n N u bit)))
  intro x
  exact liftedMultiplicationStep_eq_gateList m n N u bit x

/-- The exponent control bit is disjoint from every gate in the lifted
multiplication list. -/
theorem controlDisjoint (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    ∀ gate, gate ∈ liftedMultiplicationGates m n N u bit →
      EncodedBit.GateSpec.bitDisjoint (rawExponentBit m n bit) gate := by
  intro gate hgate
  rw [liftedMultiplicationGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, _hinner, rfl⟩
  simpa [rawExponentBit, rawEncoding] using
    (EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
      (BinaryLabelEncoding.finIdentity m)
      (BinaryLabelEncoding.prod
        (MAU.Multiplication.VBECircuit.encoding n)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit))
      innerGate)

/-- The clean work bit is disjoint from every gate in the lifted
multiplication list. -/
theorem workDisjoint (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    ∀ gate, gate ∈ liftedMultiplicationGates m n N u bit →
      EncodedBit.GateSpec.bitDisjoint (rawControlWorkBit m n) gate := by
  intro gate hgate
  rw [liftedMultiplicationGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨sourceGate, _hsource, rfl⟩
  have hinnerDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit sourceGate
  have houterDisjoint :=
    EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint
      (BinaryLabelEncoding.finIdentity m)
      (BinaryLabelEncoding.prodRightBit
        (MAU.Multiplication.VBECircuit.encoding n)
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool sourceGate)
      hinnerDisjoint
  simpa [rawControlWorkBit, rawEncoding] using houterDisjoint

/-- The raw exponent control wire and clean work wire are distinct. -/
theorem rawControlWork_ne (m n : Nat) (bit : Fin m) :
    (rawExponentBit m n bit).wire ≠ (rawControlWorkBit m n).wire := by
  simpa [rawExponentBit, rawControlWorkBit, rawEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (BinaryLabelEncoding.finIdentity m)
      (BinaryLabelEncoding.prod
        (MAU.Multiplication.VBECircuit.encoding n)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodRightBit
        (MAU.Multiplication.VBECircuit.encoding n)
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)
      (BinaryLabelEncoding.finIdentityBit m
        (WireAddress.littleEndianWire bit))).symm

/-- The named exponent control wire and clean work wire are distinct. -/
theorem controlWork_ne (m n : Nat) (bit : Fin m) :
    (exponentBit m n bit).wire ≠ (controlWorkBit m n).wire := by
  change (rawExponentBit m n bit).wire ≠ (rawControlWorkBit m n).wire
  exact rawControlWork_ne m n bit

/-- Primitive list of one mechanically controlled VBE multiplication stage. -/
def stageGates (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    List (EncodedBit.GateSpec (rawEncoding m n)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (rawExponentBit m n bit) (rawControlWorkBit m n)
    (liftedMultiplicationGates m n N u bit)
    (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
    (rawControlWork_ne m n bit)

/-- Actual gate-level stage, compiled directly from the mechanically
controlled primitive list. -/
def stageProgram (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit (Qubits (rawEncoding m n).width) :=
  EncodedBit.GateSpec.programList
    (EncodedBit.GateSpec.controlledListWithWorkGates
      (rawExponentBit m n bit) (rawControlWorkBit m n)
      (liftedMultiplicationGates m n N u bit)
      (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
      (rawControlWork_ne m n bit))

/-- The actual full-register action of one mechanically controlled stage. -/
def stageStep (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Registers m n) : Registers m n :=
  (registersEquiv m n).symm
    (EncodedBit.GateSpec.controlledListWithWorkStep
      (rawExponentBit m n bit) (rawControlWorkBit m n)
      (liftedMultiplicationGates m n N u bit)
      (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
      (rawControlWork_ne m n bit) (registersEquiv m n x))

/-- The actual controlled stage realizes its full-register gate-list fold. -/
theorem stage_realizes
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    UnitaryCircuit.Realizes (encoding m n) (stageProgram m n N u bit)
      (stageStep m n N u bit) := by
  exact UnitaryCircuit.Realizes.relabel (registersEquiv m n)
    (EncodedBit.GateSpec.controlledListWithWorkWitness
      (rawExponentBit m n bit) (rawControlWorkBit m n)
      (liftedMultiplicationGates m n N u bit)
      (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
      (rawControlWork_ne m n bit))

/-- One selected-control stage addresses only the canonical exponentiation
register, directly from its controlled primitive list. -/
theorem stageProgram_physical_idx_subset_range
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m n N u bit).physical_idx ⊆
      List.range (encoding m n).width := by
  change
    (EncodedBit.GateSpec.programList
      (stageGates m n N u bit)).physical_idx ⊆ _
  rw [encoding_width_eq_rawEncoding_width]
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range
    (stageGates m n N u bit)





/-- A strict coordinate outside the encoded-bit X/CNOT/Toffoli language has
zero multiplicity in one mechanically controlled exponentiation stage. -/
theorem stageProgram_gate_count_zero_of_ne
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (label : Resource.GateLabel)
    (hx : label ≠ .builtin "x")
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (stageProgram m n N u bit).eventCost = 0 := by
  change ResourcePool.count (.gate label)
      (EncodedBit.GateSpec.programList
        (stageGates m n N u bit)).eventCost = 0
  exact EncodedBit.GateSpec.programList_gate_count_zero_of_ne
    (stageGates m n N u bit) label hx hcnot htoffoli



/-- The source multiplication compiler has the same ordered strict event
schedule for every compiled unit. -/
private theorem sourceMultiplicationGates_events_eq
    (n N : Nat) (left right : (ZMod N)ˣ) :
    (MAU.Multiplication.VBECircuit.multiplicationGates n N left).map
        EncodedBit.GateSpec.event =
      (MAU.Multiplication.VBECircuit.multiplicationGates n N right).map
        EncodedBit.GateSpec.event :=
  MAU.Multiplication.VBECircuit.multiplicationGates_events_eq
    n N left right



/-- Product-register lifting preserves the source gate list's exact ordered
strict event trace. -/
theorem liftedMultiplicationGates_events_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplicationGates m n N left bit).map
        EncodedBit.GateSpec.event =
      (liftedMultiplicationGates m n N right bit).map
        EncodedBit.GateSpec.event := by
  unfold liftedMultiplicationGates
  calc
    ((((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit left bit)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight
          (BinaryLabelEncoding.finIdentity m))).map
          EncodedBit.GateSpec.event) =
        ((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit left bit)).map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodRight
        (BinaryLabelEncoding.finIdentity m) _
    _ = (MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit left bit)).map EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _
    _ = (MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit right bit)).map EncodedBit.GateSpec.event :=
      sourceMultiplicationGates_events_eq n N
        (stageUnit left bit) (stageUnit right bit)
    _ = ((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit right bit)).map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          EncodedBit.GateSpec.event :=
      (EncodedBit.GateSpec.map_event_prodLeft
        BinaryLabelEncoding.bool _).symm
    _ = ((((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit right bit)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight
          (BinaryLabelEncoding.finIdentity m))).map
          EncodedBit.GateSpec.event) :=
      (EncodedBit.GateSpec.map_event_prodRight
        (BinaryLabelEncoding.finIdentity m) _).symm

/-- Clean-work control expansion depends only on the source gate's strict
event coordinate, not on wire addresses or proof fields. -/
private theorem controlledEventExpansion_eq_of_event_eq
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    {left right : EncodedBit.GateSpec physicalEncoding}
    (h : EncodedBit.GateSpec.event left = EncodedBit.GateSpec.event right) :
    EncodedBit.GateSpec.controlledEventExpansion left =
      EncodedBit.GateSpec.controlledEventExpansion right := by
  cases left <;> cases right <;>
    simp [EncodedBit.GateSpec.event,
      EncodedBit.GateSpec.controlledEventExpansion,
      Resource.GateLabel.builtin] at h ⊢

/-- Equal ordered strict event traces induce equal clean-control event
expansions. -/
private theorem flatMap_controlledEventExpansion_eq_of_map_event_eq
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ left right : List (EncodedBit.GateSpec physicalEncoding),
      left.map EncodedBit.GateSpec.event =
          right.map EncodedBit.GateSpec.event →
        left.flatMap EncodedBit.GateSpec.controlledEventExpansion =
          right.flatMap EncodedBit.GateSpec.controlledEventExpansion
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | left :: leftRest, right :: rightRest, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons,
        controlledEventExpansion_eq_of_event_eq h.1,
        flatMap_controlledEventExpansion_eq_of_map_event_eq
          leftRest rightRest h.2]



/-- Clean-work control maps equal source event traces to equal controlled event
traces. -/
private theorem stageGates_events_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (stageGates m n N left bit).map EncodedBit.GateSpec.event =
      (stageGates m n N right bit).map EncodedBit.GateSpec.event := by
  unfold stageGates
  calc
    (EncodedBit.GateSpec.controlledListWithWorkGates
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N left bit)
        (controlDisjoint m n N left bit) (workDisjoint m n N left bit)
        (rawControlWork_ne m n bit)).map EncodedBit.GateSpec.event =
      (liftedMultiplicationGates m n N left bit).flatMap
        EncodedBit.GateSpec.controlledEventExpansion :=
      EncodedBit.GateSpec.map_event_controlledListWithWorkGates
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N left bit)
        (controlDisjoint m n N left bit) (workDisjoint m n N left bit)
        (rawControlWork_ne m n bit)
    _ = (liftedMultiplicationGates m n N right bit).flatMap
        EncodedBit.GateSpec.controlledEventExpansion :=
      flatMap_controlledEventExpansion_eq_of_map_event_eq
        (liftedMultiplicationGates m n N left bit)
        (liftedMultiplicationGates m n N right bit)
        (liftedMultiplicationGates_events_eq m n N left right bit)
    _ = (EncodedBit.GateSpec.controlledListWithWorkGates
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N right bit)
        (controlDisjoint m n N right bit) (workDisjoint m n N right bit)
        (rawControlWork_ne m n bit)).map EncodedBit.GateSpec.event :=
      (EncodedBit.GateSpec.map_event_controlledListWithWorkGates
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N right bit)
        (controlDisjoint m n N right bit) (workDisjoint m n N right bit)
        (rawControlWork_ne m n bit)).symm

/-- Register lifting changes addresses but preserves the source multiplication
event schedule. -/
private theorem liftedMultiplicationGates_events_eq_source
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplicationGates m n N u bit).map
        EncodedBit.GateSpec.event =
      (MAU.Multiplication.VBECircuit.multiplicationGates
        n N (stageUnit u bit)).map EncodedBit.GateSpec.event := by
  unfold liftedMultiplicationGates
  calc
    ((((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit u bit)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight
          (BinaryLabelEncoding.finIdentity m))).map
          EncodedBit.GateSpec.event) =
      ((MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit u bit)).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodRight
        (BinaryLabelEncoding.finIdentity m) _
    _ = (MAU.Multiplication.VBECircuit.multiplicationGates
          n N (stageUnit u bit)).map EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _

private theorem controlledEventExpansion_toffoli_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    (gate : EncodedBit.GateSpec physicalEncoding) :
    (EncodedBit.GateSpec.controlledEventExpansion gate).count
        (.gate (.builtin "toffoli")) =
      EncodedBit.GateSpec.cnotMultiplicity gate +
        3 * EncodedBit.GateSpec.toffoliMultiplicity gate := by
  cases gate <;> rfl

private theorem controlledEventExpansion_cnot_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    (gate : EncodedBit.GateSpec physicalEncoding) :
    (EncodedBit.GateSpec.controlledEventExpansion gate).count
        (.gate (.builtin "cnot")) =
      EncodedBit.GateSpec.xMultiplicity gate := by
  cases gate <;> rfl

private theorem flatMap_controlledEventExpansion_toffoli_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ gates : List (EncodedBit.GateSpec physicalEncoding),
      (gates.flatMap EncodedBit.GateSpec.controlledEventExpansion).count
          (.gate (.builtin "toffoli")) =
        (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
          3 * (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.flatMap_cons, List.count_append, List.map_cons,
        List.sum_cons, controlledEventExpansion_toffoli_count,
        flatMap_controlledEventExpansion_toffoli_count]
      omega

private theorem flatMap_controlledEventExpansion_cnot_count
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ gates : List (EncodedBit.GateSpec physicalEncoding),
      (gates.flatMap EncodedBit.GateSpec.controlledEventExpansion).count
          (.gate (.builtin "cnot")) =
        (gates.map EncodedBit.GateSpec.xMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.flatMap_cons, List.count_append, List.map_cons,
        List.sum_cons, controlledEventExpansion_cnot_count,
        flatMap_controlledEventExpansion_cnot_count]

private theorem controlledEventExpansion_length
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    (gate : EncodedBit.GateSpec physicalEncoding) :
    (EncodedBit.GateSpec.controlledEventExpansion gate).length =
      EncodedBit.GateSpec.xMultiplicity gate +
        EncodedBit.GateSpec.cnotMultiplicity gate +
          3 * EncodedBit.GateSpec.toffoliMultiplicity gate := by
  cases gate <;> rfl

private theorem flatMap_controlledEventExpansion_length
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical} :
    ∀ gates : List (EncodedBit.GateSpec physicalEncoding),
      (gates.flatMap EncodedBit.GateSpec.controlledEventExpansion).length =
        (gates.map EncodedBit.GateSpec.xMultiplicity).sum +
          (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
            3 * (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, controlledEventExpansion_length,
        flatMap_controlledEventExpansion_length]
      omega

/-- One controlled exponentiation stage has at most the source CNOT count plus
three times its exact source Toffoli count. -/
theorem stageProgram_toffoli_count_le
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (stageProgram m n N u bit).eventCost ≤
      228 * n ^ 2 + 43 * n := by
  have hsourceC :=
    MAU.Multiplication.VBECircuit.multiplicationGates_cnotMultiplicity_sum_le
      n N (stageUnit u bit)
  have hsourceT :=
    MAU.Multiplication.VBECircuit.multiplicationGates_toffoliMultiplicity_sum
      n N (stageUnit u bit)
  change ResourcePool.count (.gate (.builtin "toffoli"))
      (EncodedBit.GateSpec.programList (stageGates m n N u bit)).eventCost ≤ _
  rw [EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList]
  unfold stageGates
  rw [
    EncodedBit.GateSpec.map_event_controlledListWithWorkGates,
    flatMap_controlledEventExpansion_toffoli_count]
  have hc := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit)
  have ht := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit)
  rw [hc, ht, hsourceT]
  nlinarith

/-- Exact CNOT coordinate of one controlled exponentiation stage.  It is the
exact X coordinate of the source multiplication schedule. -/
theorem stageProgram_cnot_count_eq
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (stageProgram m n N u bit).eventCost = 2 * n := by
  have hsourceX :=
    MAU.Multiplication.VBECircuit.multiplicationGates_xMultiplicity_sum
      n N (stageUnit u bit)
  change ResourcePool.count (.gate (.builtin "cnot"))
      (EncodedBit.GateSpec.programList (stageGates m n N u bit)).eventCost = _
  rw [EncodedBit.GateSpec.programList_eventCost,
    ResourcePool.count_ofList]
  unfold stageGates
  rw [
    EncodedBit.GateSpec.map_event_controlledListWithWorkGates,
    flatMap_controlledEventExpansion_cnot_count]
  rw [EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit), hsourceX]









/-- Bit-pattern-independent strict-event bound for one controlled
multiplication stage. -/
theorem stageProgram_eventCount_le
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m n N u bit).eventCost.card ≤
      228 * n ^ 2 + 45 * n := by
  have hsourceX :=
    MAU.Multiplication.VBECircuit.multiplicationGates_xMultiplicity_sum
      n N (stageUnit u bit)
  have hsourceC :=
    MAU.Multiplication.VBECircuit.multiplicationGates_cnotMultiplicity_sum_le
      n N (stageUnit u bit)
  have hsourceT :=
    MAU.Multiplication.VBECircuit.multiplicationGates_toffoliMultiplicity_sum
      n N (stageUnit u bit)
  rw [show (stageProgram m n N u bit).eventCost.card =
      (stageGates m n N u bit).length by
    exact EncodedBit.GateSpec.programList_eventCost_card _]
  have hevents := EncodedBit.GateSpec.map_event_controlledListWithWorkGates
    (rawExponentBit m n bit) (rawControlWorkBit m n)
    (liftedMultiplicationGates m n N u bit)
    (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
    (rawControlWork_ne m n bit)
  have hlength := congrArg List.length hevents
  simp only [List.length_map] at hlength
  unfold stageGates
  rw [hlength, flatMap_controlledEventExpansion_length]
  have hx := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit)
  have hc := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit)
  have ht := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    (liftedMultiplicationGates_events_eq_source m n N u bit)
  rw [hx, hc, ht, hsourceX, hsourceT]
  nlinarith





/-- Register lifting preserves the strict event pool of an actual VBE
multiplication schedule across compiled units. -/
theorem liftedMultiplicationProgram_eventCost_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplicationProgram m n N left bit).eventCost =
      (liftedMultiplicationProgram m n N right bit).eventCost := by
  unfold liftedMultiplicationProgram
  apply EncodedBit.GateSpec.programList_eventCost_eq_of_events_eq
  exact liftedMultiplicationGates_events_eq m n N left right bit

/-- Register lifting preserves the strict event critical path of an actual
VBE multiplication schedule across compiled units. -/
theorem liftedMultiplicationProgram_eventDepth_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (liftedMultiplicationProgram m n N left bit).eventDepth =
      (liftedMultiplicationProgram m n N right bit).eventDepth := by
  unfold liftedMultiplicationProgram
  apply EncodedBit.GateSpec.programList_eventDepth_eq_of_events_eq
  exact liftedMultiplicationGates_events_eq m n N left right bit





/-- One controlled exponentiation stage has a strict event pool independent
of the internally selected base unit. -/
theorem stageProgram_eventCost_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m n N left bit).eventCost =
      (stageProgram m n N right bit).eventCost := by
  change
    (EncodedBit.GateSpec.programList
      (stageGates m n N left bit)).eventCost =
      (EncodedBit.GateSpec.programList
        (stageGates m n N right bit)).eventCost
  apply EncodedBit.GateSpec.programList_eventCost_eq_of_events_eq
  exact stageGates_events_eq m n N left right bit

/-- One controlled exponentiation stage has a strict event critical path
independent of the internally selected base unit. -/
theorem stageProgram_eventDepth_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) (bit : Fin m) :
    (stageProgram m n N left bit).eventDepth =
      (stageProgram m n N right bit).eventDepth := by
  change
    (EncodedBit.GateSpec.programList
      (stageGates m n N left bit)).eventDepth =
      (EncodedBit.GateSpec.programList
        (stageGates m n N right bit)).eventDepth
  apply EncodedBit.GateSpec.programList_eventDepth_eq_of_events_eq
  exact stageGates_events_eq m n N left right bit

/-- The lifted, uncontrolled semantic step maps a clean multiplication
workspace to the clean static-product endpoint. -/
theorem liftedMultiplicationStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Data m N) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    liftedMultiplicationStep m n N u bit (cleanRegisters m n N x) =
      cleanRegisters m n N (multiplicationAction u bit x) := by
  simp only [liftedMultiplicationStep, cleanRegisters, multiplicationAction]
  rw [MAU.Multiplication.VBECircuit.multiplicationStep_multiplyByUnit
    n N (stageUnit u bit) x.target hNpos hN]
  rfl

/-- Clean endpoint of one actual controlled VBE multiplication stage. -/
theorem stageStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (bit : Fin m)
    (x : Data m N) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    stageStep m n N u bit (cleanRegisters m n N x) =
      cleanRegisters m n N (stageAction u bit x) := by
  cases hcontrol : x.exponent.val.testBit bit.val
  · have hfalse :=
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N u bit)
        (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
        (rawControlWork_ne m n bit)
        (registersEquiv m n (cleanRegisters m n N x))
        (by simpa [cleanRegisters, registersEquiv] using hcontrol)
    change
      (registersEquiv m n).symm
          (EncodedBit.GateSpec.controlledListWithWorkStep
            (rawExponentBit m n bit) (rawControlWorkBit m n)
            (liftedMultiplicationGates m n N u bit)
            (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
            (rawControlWork_ne m n bit)
            (registersEquiv m n (cleanRegisters m n N x))) = _
    rw [hfalse]
    simp [cleanRegisters, registersEquiv, stageAction, selectedUnit, hcontrol]
  · have htrue :=
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
        (rawExponentBit m n bit) (rawControlWorkBit m n)
        (liftedMultiplicationGates m n N u bit)
        (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
        (rawControlWork_ne m n bit)
        (registersEquiv m n (cleanRegisters m n N x))
        (by simpa [cleanRegisters, registersEquiv] using hcontrol)
        (by simp [cleanRegisters, registersEquiv])
    change
      (registersEquiv m n).symm
          (EncodedBit.GateSpec.controlledListWithWorkStep
            (rawExponentBit m n bit) (rawControlWorkBit m n)
            (liftedMultiplicationGates m n N u bit)
            (controlDisjoint m n N u bit) (workDisjoint m n N u bit)
            (rawControlWork_ne m n bit)
            (registersEquiv m n (cleanRegisters m n N x))) = _
    rw [htrue,
      liftedMultiplicationStep_eq_gateList,
      liftedMultiplicationStep_cleanEndpoint m n N u bit x hNpos hN]
    apply congrArg (cleanRegisters m n N)
    apply Data.ext
    · rfl
    · simp [multiplicationAction, stageAction, selectedUnit, hcontrol]
/-! ### Fixed full-exponent fold -/

/-- Semantic accumulator state after the selected list of exponent stages. -/
def applyBits {m N : Nat} (u : (ZMod N)ˣ) (bits : List (Fin m))
    (x : Data m N) : Data m N where
  exponent := x.exponent
  target := (scheduledUnit u x.exponent.val bits : ZMod N) * x.target

/-- Concatenate actual controlled multiplication stages in list order. -/
def programForBits (m n N : Nat) (u : (ZMod N)ˣ) :
    List (Fin m) → UnitaryCircuit (Qubits (rawEncoding m n).width)
  | [] => UnitaryCircuit.identity (Qubits (rawEncoding m n).width) [] (by simp)
  | bit :: rest =>
      UnitaryCircuit.seq (stageProgram m n N u bit)
        (programForBits m n N u rest)

/-- Every fixed selected-bit schedule stays inside the one canonical
exponentiation register. -/
theorem programForBits_physical_idx_subset_range
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m n N u bits).physical_idx ⊆
        List.range (encoding m n).width
  | [] => by
      intro index hindex
      simp [programForBits, UnitaryCircuit.identity] at hindex
  | bit :: rest => by
      intro index hindex
      change index ∈ UnitaryCircuit.unionPhysicalIdx
        (stageProgram m n N u bit).physical_idx
        (programForBits m n N u rest).physical_idx at hindex
      rcases List.mem_union_iff.mp hindex with hstage | hrest
      · exact stageProgram_physical_idx_subset_range m n N u bit hstage
      · exact programForBits_physical_idx_subset_range m n N u rest hrest



/-- A strict coordinate outside X/CNOT/Toffoli remains absent from every
fixed exponent-bit schedule. -/
theorem programForBits_gate_count_zero_of_ne
    (m n N : Nat) (u : (ZMod N)ˣ)
    (label : Resource.GateLabel)
    (hx : label ≠ .builtin "x")
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ∀ bits : List (Fin m),
      ResourcePool.count (.gate label)
        (programForBits m n N u bits).eventCost = 0
  | [] => by simp [programForBits]
  | bit :: rest => by
      simp only [programForBits, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add,
        stageProgram_gate_count_zero_of_ne m n N u bit label
          hx hcnot htoffoli,
        programForBits_gate_count_zero_of_ne m n N u label
          hx hcnot htoffoli rest,
        Nat.zero_add]

/-- Full-register semantic fold aligned with `programForBits`. -/
def programForBitsStep (m n N : Nat) (u : (ZMod N)ˣ) :
    List (Fin m) → Registers m n → Registers m n
  | [] => id
  | bit :: rest => fun x =>
      programForBitsStep m n N u rest (stageStep m n N u bit x)

/-- Every scheduled actual stage realizes the corresponding semantic fold. -/
theorem programForBits_realizes
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      UnitaryCircuit.Realizes (encoding m n) (programForBits m n N u bits)
        (programForBitsStep m n N u bits)
  | [] => by
      apply UnitaryCircuit.Realizes.congrStep
        (UnitaryCircuit.Realizes.relabel (registersEquiv m n)
          (UnitaryCircuit.Realizes.identity (rawEncoding m n)))
      intro x
      exact (registersEquiv m n).symm_apply_apply x
  | bit :: rest => by
      exact UnitaryCircuit.Realizes.seq
        (firstStep := stageStep m n N u bit)
        (secondStep := programForBitsStep m n N u rest)
        (stage_realizes m n N u bit)
        (programForBits_realizes m n N u rest)





/-- A fixed exponent-bit schedule has at most one controlled multiplication
bound for every scheduled bit. -/
theorem programForBits_eventCount_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m n N u bits).eventCost.card ≤
        bits.length * (228 * n ^ 2 + 45 * n)
  | [] => by simp [programForBits]
  | bit :: rest => by
      have hstage := stageProgram_eventCount_le m n N u bit
      have hrest := programForBits_eventCount_le m n N u rest
      simp only [programForBits, UnitaryCircuit.seq_eventCost, Multiset.card_add]
      calc
        (stageProgram m n N u bit).eventCost.card +
              (programForBits m n N u rest).eventCost.card ≤
            (228 * n ^ 2 + 45 * n) +
              rest.length * (228 * n ^ 2 + 45 * n) :=
          Nat.add_le_add hstage hrest
        _ = (bit :: rest).length * (228 * n ^ 2 + 45 * n) := by
          simp [Nat.add_mul, Nat.add_comm]







/-- Any fixed exponent-bit schedule has a strict event pool independent of
the base unit. -/
theorem programForBits_eventCost_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m n N left bits).eventCost =
        (programForBits m n N right bits).eventCost
  | [] => rfl
  | bit :: rest => by
      change
        (stageProgram m n N left bit).eventCost +
            (programForBits m n N left rest).eventCost =
          (stageProgram m n N right bit).eventCost +
            (programForBits m n N right rest).eventCost
      rw [stageProgram_eventCost_eq, programForBits_eventCost_eq]

/-- Any fixed exponent-bit schedule has a strict event critical path
independent of the base unit. -/
theorem programForBits_eventDepth_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      (programForBits m n N left bits).eventDepth =
        (programForBits m n N right bits).eventDepth
  | [] => rfl
  | bit :: rest => by
      change
        DepthExpr.seq (stageProgram m n N left bit).eventDepth
            (programForBits m n N left rest).eventDepth =
          DepthExpr.seq (stageProgram m n N right bit).eventDepth
            (programForBits m n N right rest).eventDepth
      rw [stageProgram_eventDepth_eq, programForBits_eventDepth_eq]

/-- Any fixed bit list applies exactly the product of its selected static
powers while restoring the shared multiplication workspace after every stage. -/
theorem programForBitsStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (bits : List (Fin m))
    (x : Data m N) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    programForBitsStep m n N u bits (cleanRegisters m n N x) =
      cleanRegisters m n N (applyBits u bits x) := by
  induction bits generalizing x with
  | nil =>
      simp [programForBitsStep, applyBits, scheduledUnit, cleanRegisters]
  | cons bit rest ih =>
      change programForBitsStep m n N u rest
          (stageStep m n N u bit (cleanRegisters m n N x)) = _
      rw [stageStep_cleanEndpoint m n N u bit x hNpos hN,
        ih (stageAction u bit x)]
      apply congrArg (cleanRegisters m n N)
      apply Data.ext
      · rfl
      · cases hbit : x.exponent.val.testBit bit.val
        · simp [applyBits, stageAction, scheduledUnit, selectedUnit, hbit]
        · simp [applyBits, stageAction, scheduledUnit, selectedUnit, hbit]
          ac_rfl

/-- Static list of all exponent wires in increasing little-endian index order. -/
def exponentBits (m : Nat) : List (Fin m) :=
  List.ofFn fun bit : Fin m => bit

/-- One input-independent indexed product containing all controlled VBE
multiplications.  Its parameters are only layout, modulus, and base data. -/
def exponentiationProgram (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (rawEncoding m n).width) :=
  UnitaryCircuit.indexedProductNamed "mau-exponentiation" m
    (UnitaryCircuit.identity (Qubits (rawEncoding m n).width) [] (by simp))
    (stageProgram m n N u)



/-- The actual full exponentiation program stays inside its canonical flat
register. -/
theorem exponentiationProgram_physical_idx_subset_range
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (exponentiationProgram m n N u).physical_idx ⊆
      List.range (encoding m n).width := by
  unfold exponentiationProgram UnitaryCircuit.indexedProductNamed
  apply UnitaryCircuit.foldl_unionPhysicalIdx_subset
  · intro index hindex
    simp [UnitaryCircuit.identity] at hindex
  · intro footprint hfootprint
    obtain ⟨bit, rfl⟩ := List.mem_ofFn.mp hfootprint
    exact stageProgram_physical_idx_subset_range m n N u bit

private theorem resourcePool_count_finset_sum
    {kind : ProblemKind} {Index : Type} [Fintype Index]
    (focus : Resource.Event kind) (pool : Index → ResourcePool kind) :
    ResourcePool.count focus (∑ index, pool index) =
      ∑ index, ResourcePool.count focus (pool index) := by
  classical
  have aux : ∀ indices : Finset Index,
      ResourcePool.count focus (∑ index ∈ indices, pool index) =
        ∑ index ∈ indices, ResourcePool.count focus (pool index) := by
    intro indices
    induction indices using Finset.induction with
    | empty => simp
    | @insert index rest hindex ih =>
        simp [Finset.sum_insert, hindex, ResourcePool.count_add, ih]
  simpa using aux Finset.univ





/-- The actual full exponentiation contains no strict gate coordinate outside
the source X/CNOT/Toffoli language. -/
theorem exponentiationProgram_gate_count_zero_of_ne
    (m n N : Nat) (u : (ZMod N)ˣ)
    (label : Resource.GateLabel)
    (hx : label ≠ .builtin "x")
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label)
        (exponentiationProgram m n N u).eventCost = 0 := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add]
  rw [resourcePool_count_finset_sum]
  exact Finset.sum_eq_zero fun bit _ =>
    stageProgram_gate_count_zero_of_ne
      m n N u bit label hx hcnot htoffoli

/-- The complete fixed-layout exponentiation program has one quadratic
multiplication bound for every exponent bit. -/
theorem exponentiationProgram_eventCount_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (exponentiationProgram m n N u).eventCost.card ≤
      m * (228 * n ^ 2 + 45 * n) := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add, Multiset.card_sum]
  calc
    (∑ bit : Fin m, (stageProgram m n N u bit).eventCost.card) ≤
        ∑ _bit : Fin m, (228 * n ^ 2 + 45 * n) :=
      Finset.sum_le_sum fun bit _ => stageProgram_eventCount_le m n N u bit
    _ = m * (228 * n ^ 2 + 45 * n) := by simp

/-- Toffoli-only bound of the indexed exponentiation product. -/
theorem exponentiationProgram_toffoli_count_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (exponentiationProgram m n N u).eventCost ≤
      m * (228 * n ^ 2 + 43 * n) := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add]
  rw [resourcePool_count_finset_sum]
  calc
    (∑ bit : Fin m, ResourcePool.count (.gate (.builtin "toffoli"))
        (stageProgram m n N u bit).eventCost) ≤
      ∑ _bit : Fin m, (228 * n ^ 2 + 43 * n) :=
        Finset.sum_le_sum fun bit _ =>
          stageProgram_toffoli_count_le m n N u bit
    _ = m * (228 * n ^ 2 + 43 * n) := by simp

/-- Exact CNOT coordinate of the indexed exponentiation product. -/
theorem exponentiationProgram_cnot_count_eq
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (exponentiationProgram m n N u).eventCost =
      m * (2 * n) := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add]
  rw [resourcePool_count_finset_sum]
  simp only [stageProgram_cnot_count_eq]
  simp

private theorem unitDepth_le_eventPool_card
    (expression : DepthExpr (Resource.Event .quantum)) :
    DepthExpr.depthEval (fun _ => 1) expression ≤
      (DepthExpr.costEval (fun event => ResourcePool.singleton event)
        expression).card := by
  induction expression with
  | id => simp [DepthExpr.depthEval, DepthExpr.costEval]
  | atom event => simp [DepthExpr.depthEval, DepthExpr.costEval,
      ResourcePool.singleton]
  | seq left right leftIH rightIH =>
      simpa only [DepthExpr.depthEval_seq, DepthExpr.costEval_seq,
        Multiset.card_add] using Nat.add_le_add leftIH rightIH
  | tensor left right leftIH rightIH =>
      simp only [DepthExpr.depthEval_tensor, DepthExpr.costEval_tensor,
        Multiset.card_add]
      exact Nat.max_le.mpr
        ⟨leftIH.trans (Nat.le_add_right _ _),
          rightIH.trans (Nat.le_add_left _ _)⟩
  | inverse body bodyIH =>
      simpa only [DepthExpr.depthEval_inverse, DepthExpr.costEval_inverse]
        using bodyIH
  | controlled _ body bodyIH =>
      simpa only [DepthExpr.depthEval_controlled, DepthExpr.costEval_controlled]
        using bodyIH
  | iterate count body bodyIH =>
      simpa only [DepthExpr.depthEval_iterate, DepthExpr.costEval_iterate,
        Multiset.card_nsmul] using Nat.mul_le_mul_left count bodyIH
  | indexedProduct _ _ start step startIH stepIH =>
      simp only [DepthExpr.depthEval_indexedProduct,
        DepthExpr.costEval_indexedProduct, Multiset.card_add,
        Multiset.card_sum]
      exact Nat.add_le_add startIH
        (Finset.sum_le_sum fun index _ => stepIH index)

private theorem circuit_unitDepth_le_eventCost_card {R : Register}
    (circuit : UnitaryCircuit R) :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ circuit.eventCost.card := by
  exact (unitDepth_le_eventPool_card circuit.eventDepth).trans_eq
    (congrArg Multiset.card
      (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost circuit))

/-- Circuit-only depth of the indexed exponentiation product. -/
theorem exponentiationProgram_unitDepth_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (exponentiationProgram m n N u).evaluatedEventDepth (fun _ => 1) ≤
      m * (228 * n ^ 2 + 45 * n) :=
  (circuit_unitDepth_le_eventCost_card
    (exponentiationProgram m n N u)).trans
      (exponentiationProgram_eventCount_le m n N u)





/-- The complete actual exponentiation program has a strict event pool
independent of the internally selected base unit. -/
theorem exponentiationProgram_eventCost_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) :
    (exponentiationProgram m n N left).eventCost =
      (exponentiationProgram m n N right).eventCost := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add]
  exact Finset.sum_congr rfl fun bit _ =>
    stageProgram_eventCost_eq m n N left right bit

/-- The complete actual exponentiation program has a strict event critical
path independent of the internally selected base unit. -/
theorem exponentiationProgram_eventDepth_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) :
    (exponentiationProgram m n N left).eventDepth =
      (exponentiationProgram m n N right).eventDepth := by
  simp only [exponentiationProgram,
    UnitaryCircuit.indexedProductNamed_eventDepth,
    UnitaryCircuit.identity_eventDepth]
  congr 2
  funext bit
  exact stageProgram_eventDepth_eq m n N left right bit

private theorem sequenceList_realizes_from
    {Physical : Type} {physicalEncoding : BinaryLabelEncoding Physical}
    {start : UnitaryCircuit (Qubits physicalEncoding.width)}
    {startStep : Physical → Physical}
    (hstart : UnitaryCircuit.Realizes physicalEncoding start startStep) :
    ∀ {programs : List (UnitaryCircuit (Qubits physicalEncoding.width))}
      {steps : List (Physical → Physical)},
      List.Forall₂
          (fun program step => UnitaryCircuit.Realizes physicalEncoding program step)
          programs steps →
        UnitaryCircuit.Realizes physicalEncoding
          (UnitaryCircuit.sequenceList start programs)
          (fun x => UnitaryCircuit.Realizes.stepList steps (startStep x)) := by
  intro programs steps hprograms
  induction hprograms generalizing start startStep with
  | nil =>
      simpa [UnitaryCircuit.sequenceList, UnitaryCircuit.Realizes.stepList] using hstart
  | cons hhead htail ih =>
      simpa [UnitaryCircuit.sequenceList, UnitaryCircuit.Realizes.stepList] using
        ih (UnitaryCircuit.Realizes.seq hstart hhead)

private theorem stagePrograms_realize
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ∀ bits : List (Fin m),
      List.Forall₂
        (fun program step => UnitaryCircuit.Realizes (encoding m n) program step)
        (bits.map (stageProgram m n N u))
        (bits.map (stageStep m n N u))
  | [] => .nil
  | bit :: rest =>
      .cons (stage_realizes m n N u bit)
        (stagePrograms_realize m n N u rest)

private theorem programForBitsStep_eq_stepList
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ∀ (bits : List (Fin m)) (x : Registers m n),
      programForBitsStep m n N u bits x =
        UnitaryCircuit.Realizes.stepList
          (bits.map (stageStep m n N u)) x
  | [], _ => rfl
  | bit :: rest, x => by
      change programForBitsStep m n N u rest
          (stageStep m n N u bit x) = _
      exact programForBitsStep_eq_stepList m n N u rest
        (stageStep m n N u bit x)

/-- Folded full-register action of the exact exponentiation program. -/
def exponentiationStep (m n N : Nat) (u : (ZMod N)ˣ) :
    Registers m n → Registers m n :=
  UnitaryCircuit.Realizes.stepList
    ((exponentBits m).map (stageStep m n N u))

/-- The actual exponentiation circuit realizes its folded full-register
semantic action. -/
theorem exponentiation_realizes (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (encoding m n) (exponentiationProgram m n N u)
      (exponentiationStep m n N u) := by
  let emptyNodup : ([] : List Nat).Nodup := by simp
  let start : UnitaryCircuit (Qubits (rawEncoding m n).width) :=
    UnitaryCircuit.identity (Qubits (rawEncoding m n).width) [] emptyNodup
  let programs := (exponentBits m).map (stageProgram m n N u)
  let steps := (exponentBits m).map (stageStep m n N u)
  have hstart : UnitaryCircuit.Realizes (encoding m n) start id := by
    apply UnitaryCircuit.Realizes.congrStep
      (UnitaryCircuit.Realizes.relabel (registersEquiv m n)
        (UnitaryCircuit.Realizes.identityAt (rawEncoding m n) [] emptyNodup))
    intro x
    exact (registersEquiv m n).symm_apply_apply x
  have hsequence : UnitaryCircuit.Realizes (encoding m n)
      (UnitaryCircuit.sequenceList start programs)
      (UnitaryCircuit.Realizes.stepList steps) := by
    apply UnitaryCircuit.Realizes.congrStep
      (sequenceList_realizes_from hstart
        (stagePrograms_realize m n N u (exponentBits m)))
    intro x
    rfl
  have hmatrix :
      ((exponentiationProgram m n N u).matrix :
          HilbertOperator (Qubits (rawEncoding m n).width)) =
        ((UnitaryCircuit.sequenceList start programs).matrix :
          HilbertOperator (Qubits (rawEncoding m n).width)) := by
    unfold exponentiationProgram
    rw [UnitaryCircuit.indexedProductNamed_matrix,
      UnitaryCircuit.sequenceList_matrix]
    simp only [start, UnitaryCircuit.identity_matrix, programs, exponentBits,
      List.map_ofFn, Function.comp_def]
    let circuits := List.ofFn fun bit : Fin m => stageProgram m n N u bit
    have hmap :
        List.ofFn (fun bit : Fin m =>
          ((stageProgram m n N u bit).matrix :
            HilbertOperator (Qubits (rawEncoding m n).width))) =
          circuits.map (fun program =>
            (program.matrix :
              HilbertOperator (Qubits (rawEncoding m n).width))) := by
      exact List.ofFn_comp'
        (fun bit : Fin m => stageProgram m n N u bit)
        (fun program =>
          (program.matrix :
            HilbertOperator (Qubits (rawEncoding m n).width)))
    have hfold : ∀ (programs : List
        (UnitaryCircuit (Qubits (rawEncoding m n).width)))
        (initial : HilbertOperator (Qubits (rawEncoding m n).width)),
        (programs.map (fun program =>
          (program.matrix :
            HilbertOperator (Qubits (rawEncoding m n).width)))).foldl
            (fun accumulated next => next * accumulated) initial =
          programs.foldl
            (fun accumulated next =>
              (next.matrix :
                HilbertOperator (Qubits (rawEncoding m n).width)) * accumulated)
            initial := by
      intro remaining initial
      induction remaining generalizing initial with
      | nil => rfl
      | cons program rest ih =>
          simpa using ih
            ((program.matrix :
              HilbertOperator (Qubits (rawEncoding m n).width)) * initial)
    change
      (List.ofFn (fun bit : Fin m =>
        ((stageProgram m n N u bit).matrix :
          HilbertOperator (Qubits (rawEncoding m n).width)))).foldl
          (fun accumulated next => next * accumulated) 1 =
        circuits.foldl
          (fun accumulated next =>
            (next.matrix :
              HilbertOperator (Qubits (rawEncoding m n).width)) * accumulated) 1
    rw [hmap]
    exact hfold circuits 1
  have hmatrixUnitary :
      (exponentiationProgram m n N u).matrix =
        (UnitaryCircuit.sequenceList start programs).matrix := by
    apply Subtype.ext
    exact hmatrix
  constructor
  intro x
  have h := hsequence.apply_encoded_ket x
  change
    (exponentiationProgram m n N u).matrix.apply
        (NormalizedVector.ket ((rawEncoding m n).encode
          (registersEquiv m n x))) = _
  rw [hmatrixUnitary]
  simpa only [UnitaryCircuit.applyNormalized, encoding, BinaryLabelEncoding.relabel,
    exponentiationStep, steps] using h

/-- The complete fixed program realizes the semantic modular-exponentiation
accumulator action on every clean physical input. -/
theorem exponentiationStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (x : Data m N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    exponentiationStep m n N u (cleanRegisters m n N x) =
      cleanRegisters m n N (x.applyUnit u) := by
  rw [exponentiationStep, ← programForBitsStep_eq_stepList,
    programForBitsStep_cleanEndpoint m n N u (exponentBits m)
      x hNpos hN]
  apply congrArg (cleanRegisters m n N)
  apply Data.ext
  · rfl
  · simp [applyBits, exponentBits, Data.applyUnit,
      scheduledUnit_all_eq_pow]

/-- The exact complete exponentiation circuit. -/
def exponentiationCircuit (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (rawEncoding m n).width) :=
  exponentiationProgram m n N u

/-- Clean normalized-vector endpoint of the same circuit used for all resource
projections. -/
theorem exponentiationCircuit_applyNormalized_clean_ket
    (m n N : Nat) (u : (ZMod N)ˣ) (x : Data m N)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (exponentiationCircuit m n N u).applyNormalized
        (NormalizedVector.ket
          ((encoding m n).encode (cleanRegisters m n N x))) =
      NormalizedVector.ket
        ((encoding m n).encode (cleanRegisters m n N (x.applyUnit u))) := by
  have h := (exponentiation_realizes m n N u).apply_encoded_ket
    (cleanRegisters m n N x)
  rw [exponentiationStep_cleanEndpoint m n N u x hNpos hN] at h
  change
    (exponentiationProgram m n N u).applyNormalized
        (NormalizedVector.ket
          ((encoding m n).encode (cleanRegisters m n N x))) = _
  exact h

/-! ### Reversible compute-copy-uncompute interface -/

/-- Public output word paired with the complete exponentiation workspace. -/
abbrev ReversibleRegisters (m n : Nat) :=
  Registers m n × Nat.FixedWidth.Word n

/-- Binary encoding of the exponentiation workspace and the independent XOR
output word. -/
abbrev reversibleEncoding (m n : Nat) :
    BinaryLabelEncoding (ReversibleRegisters m n) :=
  BinaryLabelEncoding.prod (encoding m n)
    (BinaryLabelEncoding.finIdentity n)

instance reversibleRegistersFinite (m n : Nat) :
    Finite (ReversibleRegisters m n) :=
  Finite.of_injective (reversibleEncoding m n).encode
    (reversibleEncoding m n).encode_injective

instance reversibleRegistersNonempty (m n : Nat) :
    Nonempty (ReversibleRegisters m n) :=
  ⟨(cleanRegisters m n 1
      { exponent := 0
        target := 0 },
    0)⟩

/-- Exact width of the public compute-copy-uncompute interface. -/
theorem reversibleEncoding_width (m n : Nat) :
    (reversibleEncoding m n).width = m + 6 * n + 5 := by
  change (encoding m n).width + n = _
  rw [encoding_width]
  omega

/-- Logical basis transport from the private VBE workspace carrier to the
fixed public qubit width. -/
private def publicIndexEquiv (m n : Nat) :
    Fin (2 ^ (reversibleEncoding m n).width) ≃
      Fin (2 ^ (m + 6 * n + 5)) :=
  Equiv.cast (congrArg (fun width => Fin (2 ^ width))
    (reversibleEncoding_width m n))

/-- Multiplication-result bit before the named exponentiation-register
relabeling. -/
def rawResultBit (m n : Nat) (bit : Fin n) :
    EncodedBit (rawEncoding m n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity m)
    (BinaryLabelEncoding.prod
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit
      (MAU.Multiplication.VBECircuit.encoding n)
      BinaryLabelEncoding.bool
      ((MAU.Multiplication.VBECircuit.multiplicandWord n).bit bit))

/-- Multiplication-result bit in the named exponentiation register. -/
def resultBit (m n : Nat) (bit : Fin n) :
    EncodedBit (encoding m n) :=
  (rawResultBit m n bit).relabel (registersEquiv m n)

@[simp] theorem resultBit_get (m n : Nat) (bit : Fin n)
    (x : Registers m n) :
    (resultBit m n bit).get x =
      x.multiplication.multiplicand.val.testBit bit.val := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bit).get
        x.multiplication = _
  exact MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get
    n bit x.multiplication

/-- Computed modular-power word, lifted into the left side of the public
interface. -/
def reversibleSourceWord (m n : Nat) :
    EncodedBit.Word (reversibleEncoding m n) n where
  bit := fun bit => BinaryLabelEncoding.prodLeftBit
    (encoding m n) (BinaryLabelEncoding.finIdentity n)
    (resultBit m n bit)

/-- Independent public output word on the right side of the interface. -/
def reversibleTargetWord (m n : Nat) :
    EncodedBit.Word (reversibleEncoding m n) n where
  bit := fun bit => BinaryLabelEncoding.prodRightBit
    (encoding m n) (BinaryLabelEncoding.finIdentity n)
    (BinaryLabelEncoding.finIdentityBit n
      (WireAddress.littleEndianWire bit))

/-- Source and target words occupy disjoint product-register fields. -/
theorem reversibleSourceTarget_ne (m n : Nat) :
    ∀ bit,
      ((reversibleSourceWord m n).bit bit).wire ≠
        ((reversibleTargetWord m n).bit bit).wire := by
  intro bit
  change
    (BinaryLabelEncoding.prodLeftBit
      (encoding m n) (BinaryLabelEncoding.finIdentity n)
      (resultBit m n bit)).wire ≠
    (BinaryLabelEncoding.prodRightBit
      (encoding m n) (BinaryLabelEncoding.finIdentity n)
      (BinaryLabelEncoding.finIdentityBit n
        (WireAddress.littleEndianWire bit))).wire
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (encoding m n) (BinaryLabelEncoding.finIdentity n)
    (BinaryLabelEncoding.finIdentityBit n
      (WireAddress.littleEndianWire bit))
    (resultBit m n bit)).symm

/-- Width-preserving XOR on public output labels. -/
def xorWord {n : Nat} (left right : Nat.FixedWidth.Word n) :
    Nat.FixedWidth.Word n :=
  ⟨left.val ^^^ right.val,
    Nat.xor_lt_two_pow left.isLt right.isLt⟩

@[simp] theorem xorWord_val {n : Nat}
    (left right : Nat.FixedWidth.Word n) :
    (xorWord left right).val = left.val ^^^ right.val :=
  rfl

theorem xorWord_testBit {n : Nat}
    (left right : Nat.FixedWidth.Word n) (bit : Fin n) :
    (xorWord left right).val.testBit bit.val =
      (left.val.testBit bit.val ^^ right.val.testBit bit.val) := by
  exact Nat.testBit_xor left.val right.val bit.val

/-- Bitwise copy from the computed result word into the public output word. -/
def reversibleCopyProgram (m n : Nat) :
    UnitaryCircuit (Qubits (reversibleEncoding m n).width) :=
  EncodedBit.Word.xorIntoProgram
    (reversibleSourceWord m n) (reversibleTargetWord m n)
    (reversibleSourceTarget_ne m n)

/-- Semantic fold of the public bitwise copy. -/
def reversibleCopyStep (m n : Nat) :
    ReversibleRegisters m n → ReversibleRegisters m n :=
  EncodedBit.Word.xorIntoStep
    (reversibleSourceWord m n) (reversibleTargetWord m n)
    (reversibleSourceTarget_ne m n)

/-- The physical low-`n` multiplication result interpreted as an output
label. -/
def physicalResultWord {m n : Nat} (x : Registers m n) :
    Nat.FixedWidth.Word n :=
  ⟨x.multiplication.multiplicand.val, ZMod.val_lt _⟩

@[simp] theorem reversibleSourceWord_get (m n : Nat) (bit : Fin n)
    (x : ReversibleRegisters m n) :
    ((reversibleSourceWord m n).bit bit).get x =
      (physicalResultWord x.1).val.testBit bit.val := by
  exact resultBit_get m n bit x.1

@[simp] theorem reversibleTargetWord_get (m n : Nat) (bit : Fin n)
    (x : ReversibleRegisters m n) :
    ((reversibleTargetWord m n).bit bit).get x =
      x.2.val.testBit bit.val := by
  change x.2.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem reversibleTargetWord_pairwise_ne (m n : Nat) :
    ∀ left right : Fin n, left ≠ right →
      ((reversibleTargetWord m n).bit left).wire ≠
        ((reversibleTargetWord m n).bit right).wire := by
  intro left right hne
  exact EncodedBit.GateSpec.prodRightWire_ne (encoding m n)
    (by
      intro hwire
      apply hne
      change WireAddress.littleEndianWire left =
        WireAddress.littleEndianWire right at hwire
      have hbit := congrArg WireAddress.bitIndex hwire
      simpa using hbit)

private theorem reversibleTargetSource_cross_ne (m n : Nat) :
    ∀ sourceBit targetBit : Fin n,
      ((reversibleTargetWord m n).bit targetBit).wire ≠
        ((reversibleSourceWord m n).bit sourceBit).wire := by
  intro sourceBit targetBit
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (encoding m n) (BinaryLabelEncoding.finIdentity n)
    (BinaryLabelEncoding.finIdentityBit n
      (WireAddress.littleEndianWire targetBit))
    (resultBit m n sourceBit)

/-- The copy fold preserves the complete workspace and XORs its physical
result word into the independent output label. -/
theorem reversibleCopyStep_eq (m n : Nat) (x : Registers m n)
    (target : Nat.FixedWidth.Word n) :
    reversibleCopyStep m n (x, target) =
      (x, xorWord target (physicalResultWord x)) := by
  apply Prod.ext
  · exact EncodedBit.Word.xorIntoStep_preserves_projection
      (reversibleSourceWord m n) (reversibleTargetWord m n)
      (reversibleSourceTarget_ne m n) (fun state => state.1)
      (fun _ _ => rfl) (x, target)
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorIntoStep_get_target
      (reversibleSourceWord m n) (reversibleTargetWord m n)
      (reversibleSourceTarget_ne m n) bit
      (fun other hne =>
        reversibleTargetWord_pairwise_ne m n other bit hne)
      (fun other =>
        reversibleTargetSource_cross_ne m n bit other)
      (x, target)
    simpa [reversibleCopyStep, xorWord_testBit] using hread

/-- Exponentiation compute circuit lifted across the independent output
register. -/
def reversibleForwardProgram (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (reversibleEncoding m n).width) :=
  UnitaryCircuit.prodLeft (n := n) (exponentiationProgram m n N u)

/-- Semantic action of the lifted exponentiation compute circuit. -/
def reversibleForwardStep (m n N : Nat) (u : (ZMod N)ˣ) :
    ReversibleRegisters m n → ReversibleRegisters m n :=
  fun x => (exponentiationStep m n N u x.1, x.2)

theorem reversibleForward_realizes (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (reversibleEncoding m n)
      (reversibleForwardProgram m n N u)
      (reversibleForwardStep m n N u) := by
  exact UnitaryCircuit.Realizes.prodLeft
    (right := BinaryLabelEncoding.finIdentity n)
    (exponentiation_realizes m n N u)

/-- Selected semantic inverse of a realized finite permutation. -/
noncomputable def realizedInverseStep {Physical : Type}
    (step : Physical → Physical) [Nonempty Physical] : Physical → Physical :=
  Function.invFun step

private theorem realizedInverseStep_rightInverse
    {Physical : Type} [Finite Physical] [Nonempty Physical]
    {physicalEncoding : BinaryLabelEncoding Physical}
    {program : UnitaryCircuit (Qubits physicalEncoding.width)}
    {step : Physical → Physical}
    (h : UnitaryCircuit.Realizes physicalEncoding program step) :
    ∀ x, step (realizedInverseStep step x) = x :=
  Function.rightInverse_invFun
    (Finite.surjective_of_injective h.injective)

private theorem realizedInverseStep_leftInverse
    {Physical : Type} [Finite Physical] [Nonempty Physical]
    {physicalEncoding : BinaryLabelEncoding Physical}
    {program : UnitaryCircuit (Qubits physicalEncoding.width)}
    {step : Physical → Physical}
    (h : UnitaryCircuit.Realizes physicalEncoding program step) :
    ∀ x, realizedInverseStep step (step x) = x := by
  intro x
  apply h.injective
  exact realizedInverseStep_rightInverse h (step x)

private theorem dagger_realizes_inverse
    {Physical : Type} [Finite Physical] [Nonempty Physical]
    {physicalEncoding : BinaryLabelEncoding Physical}
    {program : UnitaryCircuit (Qubits physicalEncoding.width)}
    {step : Physical → Physical}
    (h : UnitaryCircuit.Realizes physicalEncoding program step) :
    UnitaryCircuit.Realizes physicalEncoding program.dagger
      (realizedInverseStep step) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse h
    (realizedInverseStep_rightInverse h)

/-- Actual compute-copy-uncompute modular-exponentiation circuit. -/
def reversibleProgram (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit (Qubits (reversibleEncoding m n).width) :=
  UnitaryCircuit.seq (reversibleForwardProgram m n N u)
    (UnitaryCircuit.seq (reversibleCopyProgram m n)
      (reversibleForwardProgram m n N u).dagger)

/-- Total semantic permutation realized by the public reversible circuit. -/
noncomputable def reversibleStep (m n N : Nat) (u : (ZMod N)ˣ) :
    ReversibleRegisters m n → ReversibleRegisters m n :=
  fun x =>
    realizedInverseStep (reversibleForwardStep m n N u)
      (reversibleCopyStep m n (reversibleForwardStep m n N u x))

theorem reversible_realizes (m n N : Nat) (u : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (reversibleEncoding m n)
      (reversibleProgram m n N u) (reversibleStep m n N u) := by
  have hforward := reversibleForward_realizes m n N u
  have hcopy := EncodedBit.Word.xorInto_realizes
    (reversibleSourceWord m n) (reversibleTargetWord m n)
    (reversibleSourceTarget_ne m n)
  have hinverse := dagger_realizes_inverse hforward
  have hcomposed := UnitaryCircuit.Realizes.seq
    (firstStep := reversibleForwardStep m n N u)
    (secondStep := fun state =>
      realizedInverseStep (reversibleForwardStep m n N u)
        (reversibleCopyStep m n state))
    hforward
    (UnitaryCircuit.Realizes.seq
      (firstStep := reversibleCopyStep m n)
      (secondStep := realizedInverseStep
        (reversibleForwardStep m n N u))
      hcopy hinverse)
  change UnitaryCircuit.Realizes (reversibleEncoding m n)
    (UnitaryCircuit.seq (reversibleForwardProgram m n N u)
      (UnitaryCircuit.seq
        (EncodedBit.Word.xorIntoProgram
          (reversibleSourceWord m n) (reversibleTargetWord m n)
          (reversibleSourceTarget_ne m n))
        (reversibleForwardProgram m n N u).dagger)) _
  apply UnitaryCircuit.Realizes.congrStep hcomposed
  intro x
  rfl

/-! ### Clean public modular-power endpoint -/

/-- Canonical `n`-bit representative of `u^z mod N`. -/
def modularPowerWord (n N : Nat) (u : (ZMod N)ˣ) (z : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n) : Nat.FixedWidth.Word n := by
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  exact
    ⟨((u ^ z : (ZMod N)ˣ) : ZMod N).val,
      lt_trans (ZMod.val_lt _) hN⟩

/-- Clean public input: an exponent, the multiplicative identity in the VBE
workspace, and an arbitrary independent XOR target. -/
def reversibleInput (m n N : Nat) (z : Fin (2 ^ m))
    (target : Nat.FixedWidth.Word n) : ReversibleRegisters m n :=
  (cleanRegisters m n N
      { exponent := z
        target := 1 },
    target)

/-- Clean public output: the workspace is restored and `u^z mod N` is XORed
into the independent target word. -/
def reversibleOutput (m n N : Nat) (u : (ZMod N)ˣ)
    (z : Fin (2 ^ m)) (target : Nat.FixedWidth.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) : ReversibleRegisters m n :=
  (cleanRegisters m n N
      { exponent := z
        target := 1 },
    xorWord target (modularPowerWord n N u z.val hNpos hN))

/-- Public computational-basis label of a clean exponent and XOR target.  The
private VBE workspace is initialized canonically and transported to the fixed
`m + 6*n + 5`-qubit carrier. -/
public def reversibleInputLabel (m n N : Nat) (z : Fin (2 ^ m))
    (target : Nat.FixedWidth.Word n) : Fin (2 ^ (m + 6 * n + 5)) :=
  publicIndexEquiv m n
    ((reversibleEncoding m n).encode (reversibleInput m n N z target))

/-- Public computational-basis label after modular exponentiation and XOR,
with every private VBE work register restored. -/
public def reversibleOutputLabel (m n N : Nat) (u : (ZMod N)ˣ)
    (z : Fin (2 ^ m)) (target : Nat.FixedWidth.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) : Fin (2 ^ (m + 6 * n + 5)) :=
  publicIndexEquiv m n
    ((reversibleEncoding m n).encode
      (reversibleOutput m n N u z target hNpos hN))

/-- On the clean computed endpoint, the copied physical multiplication word is
the canonical representative of `u^z mod N`. -/
theorem physicalResultWord_cleanPower
    (m n N : Nat) (u : (ZMod N)ˣ) (z : Fin (2 ^ m))
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    physicalResultWord
        (cleanRegisters m n N
          (Data.applyUnit u
            { exponent := z
              target := 1 })) =
      modularPowerWord n N u z.val hNpos hN := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  apply Fin.ext
  simp only [physicalResultWord, cleanRegisters, Data.applyUnit,
    MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding,
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
    MAU.Multiplication.cleanInput, modularPowerWord, mul_one]
  exact ZMod.val_natCast_of_lt
    (lt_trans (ZMod.val_lt _) hN)

/-- The lifted compute program maps every clean public input to the computed
workspace while leaving the XOR target untouched. -/
theorem reversibleForwardStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (z : Fin (2 ^ m))
    (target : Nat.FixedWidth.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    reversibleForwardStep m n N u (reversibleInput m n N z target) =
      (cleanRegisters m n N
          (Data.applyUnit u
            { exponent := z
              target := 1 }),
        target) := by
  change
    (exponentiationStep m n N u
        (cleanRegisters m n N
          { exponent := z
            target := 1 }),
      target) = _
  rw [exponentiationStep_cleanEndpoint m n N u
    { exponent := z
      target := 1 } hNpos hN]

/-- The actual compute-copy-uncompute permutation restores every work register
and XORs the modular power into the independent target word. -/
theorem reversibleStep_cleanEndpoint
    (m n N : Nat) (u : (ZMod N)ˣ) (z : Fin (2 ^ m))
    (target : Nat.FixedWidth.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    reversibleStep m n N u (reversibleInput m n N z target) =
      reversibleOutput m n N u z target hNpos hN := by
  rw [reversibleStep,
    reversibleForwardStep_cleanEndpoint m n N u z target hNpos hN,
    reversibleCopyStep_eq,
    physicalResultWord_cleanPower m n N u z hNpos hN]
  have hinverse := realizedInverseStep_leftInverse
    (reversibleForward_realizes m n N u)
    (reversibleInput m n N z
      (xorWord target (modularPowerWord n N u z.val hNpos hN)))
  rw [reversibleForwardStep_cleanEndpoint m n N u z
    (xorWord target (modularPowerWord n N u z.val hNpos hN))
    hNpos hN] at hinverse
  exact hinverse

/-- Computational-basis action of the exact public reversible circuit. -/
theorem reversibleProgram_applyNormalized_clean_ket
    (m n N : Nat) (u : (ZMod N)ˣ) (z : Fin (2 ^ m))
    (target : Nat.FixedWidth.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (reversibleProgram m n N u).applyNormalized
        (NormalizedVector.ket
          ((reversibleEncoding m n).encode
            (reversibleInput m n N z target))) =
      NormalizedVector.ket
        ((reversibleEncoding m n).encode
          (reversibleOutput m n N u z target hNpos hN)) := by
  have h := (reversible_realizes m n N u).apply_encoded_ket
    (reversibleInput m n N z target)
  rw [reversibleStep_cleanEndpoint m n N u z target hNpos hN] at h
  exact h

/-! ### Circuit-derived recurrence and resource projections -/

/-- The copy layer has one strict event for every output bit. -/
theorem reversibleCopyProgram_eventCost_card (m n : Nat) :
    (reversibleCopyProgram m n).eventCost.card = n := by
  change
    (EncodedBit.GateSpec.programList
      (EncodedBit.Word.xorIntoGates
        (reversibleSourceWord m n) (reversibleTargetWord m n)
        (reversibleSourceTarget_ne m n))).eventCost.card = n
  rw [EncodedBit.GateSpec.programList_eventCost_card]
  simp [EncodedBit.Word.xorIntoGates]

/-- Every gate in the copy layer is a CNOT. -/
theorem reversibleCopyProgram_cnot_count_eq (m n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (reversibleCopyProgram m n).eventCost = n := by
  change
    ResourcePool.count (.gate (.builtin "cnot"))
      (EncodedBit.GateSpec.programList
        (EncodedBit.Word.xorIntoGates
          (reversibleSourceWord m n) (reversibleTargetWord m n)
          (reversibleSourceTarget_ne m n))).eventCost = n
  rw [EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  simp only [EncodedBit.Word.xorIntoGates, List.map_ofFn]
  rw [List.sum_ofFn]
  simp

/-- The copy layer contributes no Toffoli events. -/
theorem reversibleCopyProgram_toffoli_count_eq_zero (m n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (reversibleCopyProgram m n).eventCost = 0 := by
  change
    ResourcePool.count (.gate (.builtin "toffoli"))
      (EncodedBit.GateSpec.programList
        (EncodedBit.Word.xorIntoGates
          (reversibleSourceWord m n) (reversibleTargetWord m n)
          (reversibleSourceTarget_ne m n))).eventCost = 0
  rw [EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  simp only [EncodedBit.Word.xorIntoGates, List.map_ofFn]
  rw [List.sum_ofFn]
  simp

/-- Lifting the compute circuit across the output word preserves its strict
event pool. -/
theorem reversibleForwardProgram_eventCost
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (reversibleForwardProgram m n N u).eventCost =
      (exponentiationProgram m n N u).eventCost := by
  exact UnitaryCircuit.prodLeft_eventCost _

/-- The inverse half has literally the reverse strict event trace of the
forward compute half. -/
theorem reversibleForwardProgram_dagger_eventTrace
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (reversibleForwardProgram m n N u).dagger.eventTrace =
      (reversibleForwardProgram m n N u).eventTrace.reverse := by
  exact UnitaryCircuit.dagger_eventTrace _

/-- Dagger preserves the complete strict event pool of the forward compute
half. -/
theorem reversibleForwardProgram_dagger_eventCost
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (reversibleForwardProgram m n N u).dagger.eventCost =
      (reversibleForwardProgram m n N u).eventCost := by
  exact UnitaryCircuit.dagger_eventCost _

/-- The complete public circuit has a base-independent strict event pool. -/
theorem reversibleProgram_eventCost_eq
    (m n N : Nat) (left right : (ZMod N)ˣ) :
    (reversibleProgram m n N left).eventCost =
      (reversibleProgram m n N right).eventCost := by
  simp only [reversibleProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, reversibleForwardProgram_eventCost]
  rw [exponentiationProgram_eventCost_eq m n N left right]

/-- Toffoli-only bound for the same compute-copy-uncompute circuit that
realizes the public XOR action.  The controlled multiplication and modular
exponentiation schedule follows the source Toffoli and stage construction
[VBE95, 9511018.tex:330-416]. -/
theorem reversibleProgram_toffoli_count_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (reversibleProgram m n N u).eventCost ≤
      2 * m * (228 * n ^ 2 + 43 * n) := by
  simp only [reversibleProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost, ResourcePool.count_add]
  rw [reversibleCopyProgram_toffoli_count_eq_zero]
  have hforward :
      ResourcePool.count (.gate (.builtin "toffoli"))
          (reversibleForwardProgram m n N u).eventCost ≤
        m * (228 * n ^ 2 + 43 * n) := by
    rw [reversibleForwardProgram_eventCost]
    exact exponentiationProgram_toffoli_count_le m n N u
  calc
    ResourcePool.count (.gate (.builtin "toffoli"))
          (reversibleForwardProgram m n N u).eventCost +
        (0 + ResourcePool.count (.gate (.builtin "toffoli"))
          (reversibleForwardProgram m n N u).eventCost) ≤
      m * (228 * n ^ 2 + 43 * n) +
        (0 + m * (228 * n ^ 2 + 43 * n)) :=
      Nat.add_le_add hforward (Nat.add_le_add_left hforward 0)
    _ = 2 * m * (228 * n ^ 2 + 43 * n) := by ring

/-- Circuit-only unit-event depth bound for the complete public reversible
program.  The forward stages and their explicit resetting route follow the
source exponentiation network [VBE95, 9511018.tex:372-416]. -/
theorem reversibleProgram_unitDepth_le
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (reversibleProgram m n N u).evaluatedEventDepth (fun _ => 1) ≤
      2 * m * (228 * n ^ 2 + 45 * n) + n := by
  have hforward :
      (reversibleForwardProgram m n N u).evaluatedEventDepth (fun _ => 1) ≤
        m * (228 * n ^ 2 + 45 * n) := by
    change
      (UnitaryCircuit.prodLeft (n := n) (exponentiationProgram m n N u)).evaluatedEventDepth
          (fun _ => 1) ≤
        m * (228 * n ^ 2 + 45 * n)
    rw [UnitaryCircuit.prodLeft_evaluatedEventDepth]
    exact exponentiationProgram_unitDepth_le m n N u
  have hcopy :
      (reversibleCopyProgram m n).evaluatedEventDepth (fun _ => 1) ≤ n := by
    exact (circuit_unitDepth_le_eventCost_card
      (reversibleCopyProgram m n)).trans_eq
        (reversibleCopyProgram_eventCost_card m n)
  simp only [reversibleProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_dagger]
  calc
    (reversibleForwardProgram m n N u).evaluatedEventDepth (fun _ => 1) +
        ((reversibleCopyProgram m n).evaluatedEventDepth (fun _ => 1) +
          (reversibleForwardProgram m n N u).evaluatedEventDepth
            (fun _ => 1)) ≤
      m * (228 * n ^ 2 + 45 * n) +
        (n + m * (228 * n ^ 2 + 45 * n)) :=
      Nat.add_le_add hforward (Nat.add_le_add hcopy hforward)
    _ = 2 * m * (228 * n ^ 2 + 45 * n) + n := by ring

/-- Public theorem node for fixed-layout reversible modular exponentiation.
The witness circuit, correctness action, Toffoli count, and depth projection
are all the same concrete `reversibleProgram`; its basis action is the source
modular-exponentiation action [VBE95, 9511018.tex:372-416]. -/
theorem main
    (m n N : Nat) (u : (ZMod N)ˣ)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    ∃ circuit : UnitaryCircuit (Qubits (reversibleEncoding m n).width),
      (reversibleEncoding m n).width = m + 6 * n + 5 ∧
      ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost ≤
        2 * m * (228 * n ^ 2 + 43 * n) ∧
      circuit.evaluatedEventDepth (fun _ => 1) ≤
        2 * m * (228 * n ^ 2 + 45 * n) + n ∧
      ∀ (z : Fin (2 ^ m)) (target : Nat.FixedWidth.Word n),
        circuit.applyNormalized
            (NormalizedVector.ket
              ((reversibleEncoding m n).encode
                (reversibleInput m n N z target))) =
          NormalizedVector.ket
            ((reversibleEncoding m n).encode
              (reversibleOutput m n N u z target hNpos hN)) := by
  refine ⟨reversibleProgram m n N u, reversibleEncoding_width m n,
    reversibleProgram_toffoli_count_le m n N u,
    reversibleProgram_unitDepth_le m n N u, ?_⟩
  intro z target
  exact reversibleProgram_applyNormalized_clean_ket
    m n N u z target hNpos hN

/-- RSA-2048 substitution: the standard `m = 4096`, `n = 2048` instance uses
exactly 16,389 qubits in this construction. -/
theorem rsa2048_width :
    (reversibleEncoding 4096 2048).width = 16389 := by
  rw [reversibleEncoding_width]

/-- RSA-2048 substitution of the generic Toffoli bound. -/
theorem rsa2048_toffoli_count_le
    (N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (reversibleProgram 4096 2048 N u).eventCost ≤
      7834741768192 := by
  convert reversibleProgram_toffoli_count_le 4096 2048 N u using 1
  norm_num

/-- RSA-2048 substitution of the generic circuit-only depth bound. -/
theorem rsa2048_unitDepth_le
    (N : Nat) (u : (ZMod N)ˣ) :
    (reversibleProgram 4096 2048 N u).evaluatedEventDepth (fun _ => 1) ≤
      7834775324672 := by
  convert reversibleProgram_unitDepth_le 4096 2048 N u using 1
  norm_num

/-- Ordered strict event trace of the compiled exponentiation circuit. -/
def exponentiationEventTrace (m n N : Nat) (u : (ZMod N)ˣ) :
    List (Resource.Event .quantum) :=
  (exponentiationCircuit m n N u).eventTrace

/-- Strict event pool of the compiled exponentiation circuit. -/
def exponentiationEventCost (m n N : Nat) (u : (ZMod N)ˣ) :
    ResourcePool .quantum :=
  (exponentiationCircuit m n N u).eventCost

/-- Strict symbolic event critical path of the compiled exponentiation
circuit. -/
def exponentiationEventDepth (m n N : Nat) (u : (ZMod N)ˣ) :
    DepthExpr (Resource.Event .quantum) :=
  (exponentiationCircuit m n N u).eventDepth

/-- Evaluated strict event depth of the compiled exponentiation circuit. -/
def exponentiationEvaluatedEventDepth (m n N : Nat) (u : (ZMod N)ˣ)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  (exponentiationCircuit m n N u).evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the exponentiation
circuit. -/
def exponentiationEventQueryDepth (m n N : Nat) (u : (ZMod N)ˣ)
    (focus : Resource.Event .quantum) : Nat :=
  (exponentiationCircuit m n N u).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the exponentiation event
pool. -/
def exponentiationEventGateCount (m n N : Nat) (u : (ZMod N)ˣ)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) (exponentiationCircuit m n N u).eventCost











/-- Physical qubit count of the fixed exponentiation layout. -/
@[nolint unusedArguments]
def exponentiationQubitCount (m n N : Nat) (_u : (ZMod N)ˣ) : Nat :=
  (encoding m n).width

/-- Qubit count is the fixed layout width, independent of the runtime input. -/
theorem exponentiationQubitCount_eq (m n N : Nat) (u : (ZMod N)ˣ) :
    exponentiationQubitCount m n N u = m + (5 * n + 4 + 1) := by
  exact encoding_width m n











/-- Linearizing the exact exponentiation event depth recovers its strict event
pool. -/
theorem exponentiationCircuit_resourcesFromEventDepth_eq_eventCost
    (m n N : Nat) (u : (ZMod N)ˣ) :
    (exponentiationCircuit m n N u).resourcesFromEventDepth =
      (exponentiationCircuit m n N u).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost
    (exponentiationCircuit m n N u)

end VBECircuit

/-- Public fixed-layout modular-exponentiation theorem.  The positive-width
hypotheses are retained verbatim from the registered statement; the concrete
circuit theorem proved above is stronger in both width parameters.  The
modular-power action is the VBE construction [VBE95,
9511018.tex:372-416]. -/
@[nolint unusedArguments]
public theorem main
    (m n N : Nat) (u : (ZMod N)ˣ)
    (_hm : 1 ≤ m) (_hn : 1 ≤ n)
    (hNpos : 0 < N) (hN : N < 2 ^ n) :
    ∃ circuit : UnitaryCircuit (Qubits (m + 6 * n + 5)),
      ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost ≤
        2 * m * (228 * n ^ 2 + 43 * n) ∧
      circuit.evaluatedEventDepth (fun _ => 1) ≤
        2 * m * (228 * n ^ 2 + 45 * n) + n ∧
      ∀ (z : Fin (2 ^ m)) (target : Nat.FixedWidth.Word n),
        circuit.applyNormalized
            (NormalizedVector.ket (VBECircuit.reversibleInputLabel m n N z target)) =
          NormalizedVector.ket
            (VBECircuit.reversibleOutputLabel
              m n N u z target hNpos hN) := by
  let equiv :
      (Qubits (VBECircuit.reversibleEncoding m n).width).Index ≃
        (Qubits (m + 6 * n + 5)).Index :=
    VBECircuit.publicIndexEquiv m n
  let circuit : UnitaryCircuit (Qubits (m + 6 * n + 5)) :=
    UnitaryCircuit.reindex equiv (VBECircuit.reversibleProgram m n N u)
  refine ⟨circuit, ?_, ?_, ?_⟩
  · simpa [circuit, UnitaryCircuit.reindex_eventCost] using
      VBECircuit.reversibleProgram_toffoli_count_le m n N u
  · simpa [circuit, UnitaryCircuit.evaluatedEventDepth,
      UnitaryCircuit.reindex_eventDepth] using
      VBECircuit.reversibleProgram_unitDepth_le m n N u
  · intro z target
    have h := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      equiv (VBECircuit.reversibleProgram m n N u)
      ((VBECircuit.reversibleEncoding m n).encode
        (VBECircuit.reversibleInput m n N z target))
      ((VBECircuit.reversibleEncoding m n).encode
        (VBECircuit.reversibleOutput m n N u z target hNpos hN))
      (VBECircuit.reversibleProgram_applyNormalized_clean_ket
        m n N u z target hNpos hN)
    simpa [circuit, equiv, VBECircuit.reversibleInputLabel,
      VBECircuit.reversibleOutputLabel] using h

end

end MAU.Exponentiation
end QuantumAlg

end
