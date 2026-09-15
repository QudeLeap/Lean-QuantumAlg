/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import Mathlib.Tactic

/-!
# Exact two-bit windowed modular product addition

This module implements the table-lookup step used by exact windowed modular
arithmetic.  Two quantum source bits address the three nonzero rows of the
classical table

`j * coefficient * 2^offset mod modulus`, for `j = 1, 2, 3`.

Each row is a pure unitary load/add/unload circuit.  The selected classical
constant is loaded by actual Toffoli gates, the existing exact VBE modular
adder consumes it, and the same load is reversed.  Negative address controls
are implemented by physical X gates around the row.  No measurement-based
uncomputation, approximate arithmetic, coset encoding, or opaque resource
metadata is used [Gid19, main.tex:392-426].
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.Windowed

noncomputable section

/-- The two address bits followed by the exact VBE modular-add workspace. -/
abbrev Registers (n : Nat) := MAU.Addition.VBECircuit.ControlledRegisters n

/-- Fixed physical layout inherited from the exact doubly controlled VBE
modular-add circuit. -/
abbrev encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  MAU.Addition.VBECircuit.controlledEncoding n

/-- A negative address literal is prepared by physically flipping its source
wire; a positive literal is already in the required form. -/
def preparedControl (expected actual : Bool) : Bool :=
  if expected then actual else !actual

/-- X gates that turn one desired two-bit address pattern into the positive
control pattern `11`. -/
def prepareAddressGates (n : Nat) (expectedA expectedB : Bool) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (if expectedA then [] else [.x (MAU.Addition.VBECircuit.controlABit n)]) ++
    (if expectedB then [] else [.x (MAU.Addition.VBECircuit.controlBBit n)])

/-- Folded action of the address preparation gates. -/
def prepareAddressStep (n : Nat) (expectedA expectedB : Bool) :
    Registers n -> Registers n :=
  EncodedBit.GateSpec.stepList
    (prepareAddressGates n expectedA expectedB)

/-- Actual address preparation program. -/
def prepareAddressProgram (n : Nat) (expectedA expectedB : Bool) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.GateSpec.programList
    (prepareAddressGates n expectedA expectedB)

/-- Reverse-list address restoration program. -/
def restoreAddressProgram (n : Nat) (expectedA expectedB : Bool) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.GateSpec.programList
    (prepareAddressGates n expectedA expectedB).reverse

/-- Folded action of the reverse address preparation gates. -/
def restoreAddressStep (n : Nat) (expectedA expectedB : Bool) :
    Registers n -> Registers n :=
  EncodedBit.GateSpec.stepList
    (prepareAddressGates n expectedA expectedB).reverse

theorem prepareAddress_realizes (n : Nat) (expectedA expectedB : Bool) :
    UnitaryCircuit.Realizes (encoding n)
      (prepareAddressProgram n expectedA expectedB)
      (prepareAddressStep n expectedA expectedB) :=
  EncodedBit.GateSpec.realizesList _

theorem restoreAddress_realizes (n : Nat) (expectedA expectedB : Bool) :
    UnitaryCircuit.Realizes (encoding n)
      (restoreAddressProgram n expectedA expectedB)
      (restoreAddressStep n expectedA expectedB) :=
  EncodedBit.GateSpec.realizesList _

/-- Address preparation changes only the two control fields. -/
theorem prepareAddressStep_eq (n : Nat) (expectedA expectedB : Bool)
    (state : Registers n) :
    prepareAddressStep n expectedA expectedB state =
      { state with
        externalControl := preparedControl expectedA state.externalControl
        multiplierBit := preparedControl expectedB state.multiplierBit } := by
  rcases state with ⟨externalControl, multiplierBit, arithmetic⟩
  cases expectedA <;> cases expectedB <;>
    cases externalControl <;> cases multiplierBit <;> rfl

/-- The reverse preparation list restores every input state exactly. -/
theorem restoreAddressStep_after_prepareAddressStep
    (n : Nat) (expectedA expectedB : Bool) (state : Registers n) :
    restoreAddressStep n expectedA expectedB
        (prepareAddressStep n expectedA expectedB state) = state := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (prepareAddressGates n expectedA expectedB) state

/-- One exact addressed table-row circuit: prepare negative literals, run the
existing doubly controlled load/modular-add/unload program, then restore the
address bits. -/
def rowProgram (n N : Nat) (constant : PlainAdder.Word n)
    (expectedA expectedB : Bool) : UnitaryCircuit (Qubits (encoding n).width) :=
  UnitaryCircuit.seq (prepareAddressProgram n expectedA expectedB)
    (UnitaryCircuit.seq (MAU.Addition.VBECircuit.controlledAddProgram n N constant)
      (restoreAddressProgram n expectedA expectedB))

/-- Full-register semantic action of one addressed table row. -/
def rowStep (n N : Nat) (constant : PlainAdder.Word n)
    (expectedA expectedB : Bool) (state : Registers n) : Registers n :=
  restoreAddressStep n expectedA expectedB
    (MAU.Addition.VBECircuit.controlledAddStep n N constant
      (prepareAddressStep n expectedA expectedB state))

/-- The row circuit and its semantic action come from the same three actual
program segments. -/
theorem row_realizes (n N : Nat) (constant : PlainAdder.Word n)
    (expectedA expectedB : Bool) :
    UnitaryCircuit.Realizes (encoding n)
      (rowProgram n N constant expectedA expectedB)
      (rowStep n N constant expectedA expectedB) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.seq (prepareAddress_realizes n expectedA expectedB)
      (UnitaryCircuit.Realizes.seq
        (MAU.Addition.VBECircuit.controlledAdd_realizes n N constant)
        (restoreAddress_realizes n expectedA expectedB)))
  intro state
  rfl

/-- Canonical clean row boundary with a natural-number accumulator. -/
def cleanState (n N accumulator : Nat) (addressA addressB : Bool) :
    Registers n :=
  MAU.Addition.VBECircuit.controlledCleanState n addressA addressB 0
    (N : PlainAdder.Word n)
    (accumulator : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false

/-- One addressed row adds its constant exactly when both source literals
match the requested address pattern and restores the lookup word and all VBE
work bits. -/
theorem rowStep_cleanEndpoint (n N : Nat) (constant : PlainAdder.Word n)
    (expectedA expectedB addressA addressB : Bool) (accumulator : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hconstant : constant.val < N) (haccumulator : accumulator < N) :
    rowStep n N constant expectedA expectedB
        (cleanState n N accumulator addressA addressB) =
      cleanState n N
        (((if preparedControl expectedA addressA &&
              preparedControl expectedB addressB then constant.val else 0) +
            accumulator) % N)
        addressA addressB := by
  let preparedA := preparedControl expectedA addressA
  let preparedB := preparedControl expectedB addressB
  let accumulatorWord : PlainAdder.Word n :=
    (accumulator : PlainAdder.Word n)
  let result :=
    (((if preparedA && preparedB then constant.val else 0) + accumulator) % N)
  have haccumulatorPow : accumulator < 2 ^ n := haccumulator.trans hN
  have haccumulatorWordVal : accumulatorWord.val = accumulator :=
    ZMod.val_natCast_of_lt haccumulatorPow
  have htarget :
      MAU.Addition.VBECircuit.widenWord n accumulatorWord =
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) := by
    simpa [accumulatorWord] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        n accumulator haccumulatorPow
  have hprepare :
      prepareAddressStep n expectedA expectedB
          (cleanState n N accumulator addressA addressB) =
        MAU.Addition.VBECircuit.controlledCleanState n preparedA preparedB 0
          (N : PlainAdder.Word n)
          (MAU.Addition.VBECircuit.widenWord n accumulatorWord) false := by
    rw [prepareAddressStep_eq]
    unfold cleanState MAU.Addition.VBECircuit.controlledCleanState
    rw [htarget]
  have hadd := MAU.Addition.VBECircuit.controlledAddStep_cleanEndpoint n N
    constant accumulatorWord preparedA preparedB hNpos hN hconstant
    (by simpa only [haccumulatorWordVal] using haccumulator)
  have hresultLt : result < N := Nat.mod_lt _ hNpos
  have hresultPow : result < 2 ^ n := hresultLt.trans hN
  have hresultTarget :
      (((if preparedA && preparedB then constant.val else 0) +
            accumulatorWord.val) % N : PlainAdder.Word
              (MAU.Addition.VBECircuit.AdderWidth n)) =
        (result : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) := by
    rw [haccumulatorWordVal]
  have hpreparedResult :
      prepareAddressStep n expectedA expectedB
          (cleanState n N result addressA addressB) =
        MAU.Addition.VBECircuit.controlledCleanState n preparedA preparedB 0
          (N : PlainAdder.Word n)
          (result : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) false := by
    rw [prepareAddressStep_eq]
    rfl
  unfold rowStep
  rw [hprepare, hadd, hresultTarget]
  rw [← hpreparedResult]
  exact restoreAddressStep_after_prepareAddressStep n expectedA expectedB _

/-- Classical lookup-table residue for one two-bit window row. -/
def tableConstant (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset digit : Nat) : PlainAdder.Word n :=
  ((digit * coefficient.val * 2 ^ offset) % N : PlainAdder.Word n)

theorem tableConstant_val (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset digit : Nat) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (tableConstant n N coefficient offset digit).val =
      (digit * coefficient.val * 2 ^ offset) % N := by
  exact ZMod.val_natCast_of_lt
    ((Nat.mod_lt _ hNpos).trans hN)

theorem tableConstant_lt (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset digit : Nat) (hNpos : 0 < N) (hN : N < 2 ^ n) :
    (tableConstant n N coefficient offset digit).val < N := by
  rw [tableConstant_val n N coefficient offset digit hNpos hN]
  exact Nat.mod_lt _ hNpos

/-- Three exact rows for the nonzero little-endian two-bit addresses `01`,
`10`, and `11`. -/
def windowProgram (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset : Nat) : UnitaryCircuit (Qubits (encoding n).width) :=
  UnitaryCircuit.seq
    (rowProgram n N (tableConstant n N coefficient offset 1) true false)
    (UnitaryCircuit.seq
      (rowProgram n N (tableConstant n N coefficient offset 2) false true)
      (rowProgram n N (tableConstant n N coefficient offset 3) true true))

/-- Semantic action of the three-row two-bit lookup-add program. -/
def windowStep (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset : Nat) (state : Registers n) : Registers n :=
  rowStep n N (tableConstant n N coefficient offset 3) true true
    (rowStep n N (tableConstant n N coefficient offset 2) false true
      (rowStep n N (tableConstant n N coefficient offset 1) true false state))

theorem window_realizes (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset : Nat) :
    UnitaryCircuit.Realizes (encoding n) (windowProgram n N coefficient offset)
      (windowStep n N coefficient offset) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.seq
      (row_realizes n N (tableConstant n N coefficient offset 1) true false)
      (UnitaryCircuit.Realizes.seq
        (row_realizes n N (tableConstant n N coefficient offset 2) false true)
        (row_realizes n N (tableConstant n N coefficient offset 3) true true)))
  intro state
  rfl

/-! ## Native Toffoli accounting -/

/-- A doubly controlled constant xor has exactly one Toffoli for each set bit
of the classical payload. -/
theorem doubleControlledXorConstantProgram_toffoli_count_eq
    {Data : Type} {dataEncoding : BinaryLabelEncoding Data} {width : Nat}
    (controlA controlB : EncodedBit dataEncoding)
    (target : EncodedBit.Word dataEncoding width)
    (constant : Fin (2 ^ width))
    (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit,
      controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit,
      controlB.wire ≠ (target.bit bit).wire) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (EncodedBit.Word.doubleControlledXorConstantProgram
          controlA controlB target constant hcontrols hcontrolATarget
          hcontrolBTarget).eventCost =
      (EncodedBit.Word.constantOneIndices constant).length := by
  rw [EncodedBit.Word.doubleControlledXorConstantProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold EncodedBit.Word.doubleControlledXorConstantGates
  generalize EncodedBit.Word.constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        EncodedBit.GateSpec.toffoliMultiplicity_toffoli]
      rw [show
        (List.map EncodedBit.GateSpec.toffoliMultiplicity
          (List.map
            (fun bit => EncodedBit.GateSpec.toffoli controlA controlB
              (target.bit bit) hcontrols (hcontrolATarget bit)
              (hcontrolBTarget bit)) rest)).sum = rest.length from ih]
      omega

/-- Reversing the doubly controlled load preserves its exact Toffoli count. -/
theorem doubleControlledXorConstantUnloadProgram_toffoli_count_eq
    {Data : Type} {dataEncoding : BinaryLabelEncoding Data} {width : Nat}
    (controlA controlB : EncodedBit dataEncoding)
    (target : EncodedBit.Word dataEncoding width)
    (constant : Fin (2 ^ width))
    (hcontrols : controlA.wire ≠ controlB.wire)
    (hcontrolATarget : ∀ bit,
      controlA.wire ≠ (target.bit bit).wire)
    (hcontrolBTarget : ∀ bit,
      controlB.wire ≠ (target.bit bit).wire) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (EncodedBit.Word.doubleControlledXorConstantUnloadProgram
          controlA controlB target constant hcontrols hcontrolATarget
          hcontrolBTarget).eventCost =
      (EncodedBit.Word.constantOneIndices constant).length := by
  rw [EncodedBit.Word.doubleControlledXorConstantUnloadProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  unfold EncodedBit.Word.doubleControlledXorConstantUnloadGates
  rw [List.map_reverse, List.sum_reverse]
  unfold EncodedBit.Word.doubleControlledXorConstantGates
  generalize EncodedBit.Word.constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        EncodedBit.GateSpec.toffoliMultiplicity_toffoli]
      rw [show
        (List.map EncodedBit.GateSpec.toffoliMultiplicity
          (List.map
            (fun bit => EncodedBit.GateSpec.toffoli controlA controlB
              (target.bit bit) hcontrols (hcontrolATarget bit)
              (hcontrolBTarget bit)) rest)).sum = rest.length from ih]
      omega

/-- Closed exact Toffoli coordinate of one addressed table row. -/
def rowToffoliCount (n : Nat) (constant : PlainAdder.Word n) : Nat :=
  30 * n +
    2 * (EncodedBit.Word.constantOneIndices
      (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length

theorem prepareAddressProgram_toffoli_count_eq
    (n : Nat) (expectedA expectedB : Bool) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (prepareAddressProgram n expectedA expectedB).eventCost = 0 := by
  rw [prepareAddressProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  cases expectedA <;> cases expectedB <;>
    simp [prepareAddressGates]

theorem restoreAddressProgram_toffoli_count_eq
    (n : Nat) (expectedA expectedB : Bool) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (restoreAddressProgram n expectedA expectedB).eventCost = 0 := by
  rw [restoreAddressProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  cases expectedA <;> cases expectedB <;>
    simp [prepareAddressGates]

theorem controlledLoadProgram_toffoli_count_eq
    (n : Nat) (constant : PlainAdder.Word n) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Addition.VBECircuit.controlledLoadProgram n constant).eventCost =
      (EncodedBit.Word.constantOneIndices
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length := by
  unfold MAU.Addition.VBECircuit.controlledLoadProgram
  exact doubleControlledXorConstantProgram_toffoli_count_eq _ _ _ _ _ _ _

theorem controlledUnloadProgram_toffoli_count_eq
    (n : Nat) (constant : PlainAdder.Word n) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Addition.VBECircuit.controlledUnloadProgram n constant).eventCost =
      (EncodedBit.Word.constantOneIndices
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length := by
  unfold MAU.Addition.VBECircuit.controlledUnloadProgram
  exact doubleControlledXorConstantUnloadProgram_toffoli_count_eq _ _ _ _ _ _ _

theorem controlledArithmeticProgram_toffoli_count_eq (n N : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Addition.VBECircuit.controlledArithmeticProgram n N).eventCost =
      30 * n := by
  have hcost :
      (MAU.Addition.VBECircuit.controlledArithmeticProgram n N).eventCost =
        (MAU.Addition.VBECircuit.modularAddProgram n N).eventCost := by
    exact UnitaryCircuit.prodRight_eventCost
      (m := MAU.Addition.VBECircuit.controlPairEncoding.width)
      (MAU.Addition.VBECircuit.modularAddProgram n N)
  rw [hcost]
  exact MAU.Addition.VBECircuit.modularAddProgram_toffoli_count_eq n N

theorem controlledAddProgram_toffoli_count_eq
    (n N : Nat) (constant : PlainAdder.Word n) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Addition.VBECircuit.controlledAddProgram n N constant).eventCost =
      rowToffoliCount n constant := by
  change ResourcePool.count (.gate (.builtin "toffoli"))
      ((MAU.Addition.VBECircuit.controlledLoadProgram n constant).eventCost +
        ((MAU.Addition.VBECircuit.controlledArithmeticProgram n N).eventCost +
          ((MAU.Addition.VBECircuit.controlledUnloadProgram n constant).eventCost +
            0))) = _
  rw [ResourcePool.count_add, ResourcePool.count_add,
    ResourcePool.count_add]
  rw [controlledLoadProgram_toffoli_count_eq,
    controlledArithmeticProgram_toffoli_count_eq,
    controlledUnloadProgram_toffoli_count_eq]
  simp [rowToffoliCount]
  omega

/-- The exact row Toffoli count is projected from the same physical circuit
that proves the clean endpoint. -/
theorem rowProgram_toffoli_count_eq (n N : Nat)
    (constant : PlainAdder.Word n) (expectedA expectedB : Bool) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (rowProgram n N constant expectedA expectedB).eventCost =
      rowToffoliCount n constant := by
  rw [rowProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    prepareAddressProgram_toffoli_count_eq,
    restoreAddressProgram_toffoli_count_eq,
    controlledAddProgram_toffoli_count_eq]
  omega

/-- One table row uses at most `32*n+2` Toffolis. -/
theorem rowToffoliCount_le (n : Nat) (constant : PlainAdder.Word n) :
    rowToffoliCount n constant ≤ 32 * n + 2 := by
  have hset := EncodedBit.Word.constantOneIndices_length_le
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
  simp only [MAU.Addition.VBECircuit.AdderWidth] at hset
  unfold rowToffoliCount
  omega

/-- Exact Toffoli sum of the three nonzero table rows. -/
def windowToffoliCount (n N : Nat) (coefficient : PlainAdder.Word n)
    (offset : Nat) : Nat :=
  rowToffoliCount n (tableConstant n N coefficient offset 1) +
    rowToffoliCount n (tableConstant n N coefficient offset 2) +
    rowToffoliCount n (tableConstant n N coefficient offset 3)

theorem windowProgram_toffoli_count_eq (n N : Nat)
    (coefficient : PlainAdder.Word n) (offset : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (windowProgram n N coefficient offset).eventCost =
      windowToffoliCount n N coefficient offset := by
  rw [windowProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add]
  rw [rowProgram_toffoli_count_eq, rowProgram_toffoli_count_eq,
    rowProgram_toffoli_count_eq]
  simp [windowToffoliCount, Nat.add_assoc]

/-- Width-only linear Toffoli bound for one exact two-bit lookup-add window. -/
theorem windowToffoliCount_le (n N : Nat)
    (coefficient : PlainAdder.Word n) (offset : Nat) :
    windowToffoliCount n N coefficient offset ≤ 96 * n + 6 := by
  have h1 := rowToffoliCount_le n (tableConstant n N coefficient offset 1)
  have h2 := rowToffoliCount_le n (tableConstant n N coefficient offset 2)
  have h3 := rowToffoliCount_le n (tableConstant n N coefficient offset 3)
  unfold windowToffoliCount
  omega

/-- Little-endian natural value of a two-bit address. -/
def addressValue (addressA addressB : Bool) : Nat :=
  addressA.toNat + 2 * addressB.toNat

/-- The actual three-row circuit performs one exact windowed modular product
addition and restores all lookup and VBE work registers. -/
theorem windowStep_cleanEndpoint (n N : Nat)
    (coefficient : PlainAdder.Word n) (offset accumulator : Nat)
    (addressA addressB : Bool) (hNpos : 0 < N) (hN : N < 2 ^ n)
    (haccumulator : accumulator < N) :
    windowStep n N coefficient offset
        (cleanState n N accumulator addressA addressB) =
      cleanState n N
        ((accumulator +
            addressValue addressA addressB * coefficient.val * 2 ^ offset) % N)
        addressA addressB := by
  cases addressA <;> cases addressB <;>
    simp only [windowStep]
  all_goals
    rw [rowStep_cleanEndpoint n N
      (tableConstant n N coefficient offset 1) true false _ _ accumulator
      hNpos hN (tableConstant_lt n N coefficient offset 1 hNpos hN)
      haccumulator]
    rw [rowStep_cleanEndpoint n N
      (tableConstant n N coefficient offset 2) false true _ _ _
      hNpos hN (tableConstant_lt n N coefficient offset 2 hNpos hN)
      (Nat.mod_lt _ hNpos)]
    rw [rowStep_cleanEndpoint n N
      (tableConstant n N coefficient offset 3) true true _ _ _
      hNpos hN (tableConstant_lt n N coefficient offset 3 hNpos hN)
      (Nat.mod_lt _ hNpos)]
    simp [preparedControl, addressValue,
      tableConstant_val, hNpos, hN, Nat.mod_eq_of_lt haccumulator,
      Nat.add_mod_mod, Nat.add_comm]

/-! ## Full multiplier-word layout -/

namespace FullLayout

/-- The complete multiplier word paired with the shared VBE workspace. -/
abbrev Registers (n : Nat) :=
  MAU.Multiplication.Accumulate.VBECircuit.Registers n

/-- The established `5*n+4` multiplication encoding. -/
abbrev encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  MAU.Multiplication.Accumulate.VBECircuit.encoding n

/-- Two distinct source-word bits used as one lookup address. -/
theorem sourceControls_ne (n : Nat) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) :
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA).wire ≠
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB).wire := by
  exact MAU.Multiplication.VBECircuit.multiplicand_pairwise_ne n bitA bitB hne

/-- Actual Toffoli list loading a lookup row under two source-word controls. -/
def loadGates (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  EncodedBit.Word.doubleControlledXorConstantGates
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)

/-- Physical load program on the complete multiplier layout. -/
def loadProgram (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.Word.doubleControlledXorConstantProgram
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)

/-- Folded action of the physical load list. -/
def loadStep (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n :=
  EncodedBit.Word.doubleControlledXorConstantStep
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)

theorem load_realizes (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit.Realizes (encoding n) (loadProgram n constant bitA bitB hne)
      (loadStep n constant bitA bitB hne) :=
  EncodedBit.Word.doubleControlledXorConstant_realizes _ _ _ _ _ _ _

/-- Loading into a zero active-source word selects the classical row exactly
when both addressed source bits are one, while preserving the full multiplier
and every other VBE field. -/
theorem loadStep_cleanEndpoint (n : Nat) (constant x : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
    (flag : Bool) :
    loadStep n constant bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.workspaceState
          n x 0 parked target flag) =
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
        (if x.val.testBit bitA.val && x.val.testBit bitB.val then
          constant else 0) parked target flag := by
  let input := MAU.Multiplication.Accumulate.VBECircuit.workspaceState
    n x 0 parked target flag
  let loaded : PlainAdder.Word n :=
    if x.val.testBit bitA.val && x.val.testBit bitB.val then constant else 0
  have hactive :
      (loadStep n constant bitA bitB hne input).arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord n loaded := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro sourceBit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_target
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        sourceBit
        (fun other hother =>
          MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
            n other sourceBit hother) input
    rw [show
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
          sourceBit =
        MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit n sourceBit
      from rfl] at hread
    rw [MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get] at hread
    have hconstant :=
      MAU.Addition.VBECircuit.controlledConstantLabel_testBit
        n constant sourceBit
    have hzeroBit :
        (MAU.Addition.VBECircuit.widenWord n
          (0 : PlainAdder.Word n)).val.testBit sourceBit.val = false := by
      rw [MAU.Addition.VBECircuit.widenWord_val]
      simp
    have hinputActive :
        ((MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
            sourceBit).get input = false := by
      rw [show
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
            sourceBit =
          MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit n sourceBit
        from rfl]
      rw [MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get]
      simp [input,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        MAU.Addition.VBECircuit.widenWord_val]
    cases hbitA : x.val.testBit bitA.val <;>
      cases hbitB : x.val.testBit bitB.val <;>
      cases hconstantBit :
        (MAU.Addition.VBECircuit.widenWord n constant).val.testBit
          sourceBit.val <;>
      simpa [loadStep, input,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState, loaded,
        hconstant, hzeroBit, hinputActive, hbitA, hbitB,
        hconstantBit] using hread
  have hmultiplicand :
      (loadStep n constant bitA bitB hne input).multiplicand = x := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro observedBit
    rw [← MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get]
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n observedBit)
        (fun sourceBit => Ne.symm
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
            n observedBit sourceBit)) input
    simpa [loadStep, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using hread
  have htarget :
      (loadStep n constant bitA bitB hne input).arithmetic.target = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro targetBit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit n targetBit)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
          n (MAU.Addition.VBECircuit.targetBit n targetBit)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_target_ne
              n sourceBit targetBit)) input
    simpa [loadStep, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hcarry :
      (loadStep n constant bitA bitB hne input).arithmetic.carry = false := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
          (MAU.Addition.VBECircuit.carryBit n))
        (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
          n (MAU.Addition.VBECircuit.carryBit n)
          (MAU.Addition.VBECircuit.activeSource_carry_ne n)) input
    simpa [loadStep, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hparked :
      (loadStep n constant bitA bitB hne input).arithmetic.parkedSource =
        parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro parkedBit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
          (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit))
        (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
          n (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_parked_ne
              n sourceBit parkedBit)) input
    simpa [loadStep, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hwork :
      (loadStep n constant bitA bitB hne input).arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth n) := by
    change (loadStep n constant bitA bitB hne input).arithmetic.carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    rw [← MAU.Addition.VBECircuit.carryWorkBit_get n workBit
      (loadStep n constant bitA bitB hne input).arithmetic]
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
          (MAU.Addition.VBECircuit.carryWorkBit n workBit))
        (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
          n (MAU.Addition.VBECircuit.carryWorkBit n workBit)
          (fun sourceBit =>
            MAU.Addition.VBECircuit.activeSource_carryWork_ne
              n sourceBit workBit)) input
    have hread' :
        (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            (loadStep n constant bitA bitB hne input).arithmetic =
          (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            input.arithmetic := by
      simpa [loadStep] using hread
    rw [hread', MAU.Addition.VBECircuit.carryWorkBit_get]
    simp [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag :
      (loadStep n constant bitA bitB hne input).arithmetic.reductionFlag =
        flag := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
        (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB)
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
          (MAU.Addition.VBECircuit.reductionFlagBit n))
        (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
          n (MAU.Addition.VBECircuit.reductionFlagBit n)
          (fun sourceBit => Ne.symm
            (MAU.Addition.VBECircuit.reductionFlag_activeSource_ne
              n sourceBit))) input
    simpa [loadStep, input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  change loadStep n constant bitA bitB hne input = _
  apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv n).injective
  change
    ((loadStep n constant bitA bitB hne input).multiplicand,
      (loadStep n constant bitA bitB hne input).arithmetic) =
    (x, MAU.Addition.VBECircuit.sourceSwapCleanState n loaded parked
      target flag)
  rw [hmultiplicand]
  congr 1
  rcases harithmetic :
      (loadStep n constant bitA bitB hne input).arithmetic with
    ⟨active, target', carry, parked', work, flag'⟩
  simp only [harithmetic] at hactive htarget hcarry hparked hwork hflag ⊢
  subst_vars
  rfl

/-- Reverse of the physical double-controlled load list. -/
def unloadGates (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (loadGates n constant bitA bitB hne).reverse

/-- Physical unload program on the complete multiplier layout. -/
def unloadProgram (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.Word.doubleControlledXorConstantUnloadProgram
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)

/-- Folded action of the reverse physical load list. -/
def unloadStep (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n :=
  EncodedBit.Word.doubleControlledXorConstantUnloadStep
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)

theorem unload_realizes (n : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit.Realizes (encoding n) (unloadProgram n constant bitA bitB hne)
      (unloadStep n constant bitA bitB hne) :=
  EncodedBit.Word.doubleControlledXorConstantUnload_realizes _ _ _ _ _ _ _

/-- The reverse physical list exactly removes its matching load on every
full-layout basis label. -/
theorem unloadStep_after_loadStep (n : Nat)
    (constant : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) (state : Registers n) :
    unloadStep n constant bitA bitB hne
        (loadStep n constant bitA bitB hne state) = state := by
  exact
    EncodedBit.Word.doubleControlledXorConstantUnloadStep_after_doubleControlledXorConstantStep
      _ _ _ _ _ _ _ state

/-- One full-layout exact table row: load the selected constant, apply the
established modular adder, and reverse the load. -/
def fullRowGates (n N : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  loadGates n constant bitA bitB hne ++
    MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates n N ++
    unloadGates n constant bitA bitB hne

/-- Actual circuit compiled from one complete table-row gate list. -/
def fullRowProgram (n N : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.GateSpec.programList
    (fullRowGates n N constant bitA bitB hne)

/-- Folded basis action of one complete table-row gate list. -/
def fullRowStep (n N : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n :=
  EncodedBit.GateSpec.stepList
    (fullRowGates n N constant bitA bitB hne)

theorem fullRowStep_eq_composition (n N : Nat)
    (constant : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) (state : Registers n) :
    fullRowStep n N constant bitA bitB hne state =
      unloadStep n constant bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep n N
          (loadStep n constant bitA bitB hne state)) := by
  simp only [fullRowStep, fullRowGates,
    EncodedBit.GateSpec.stepList_append]
  rw [MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep_eq_gateList]
  rfl

theorem fullRow_realizes (n N : Nat) (constant : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit.Realizes (encoding n)
      (fullRowProgram n N constant bitA bitB hne)
      (fullRowStep n N constant bitA bitB hne) :=
  EncodedBit.GateSpec.realizesList _

/-- One complete table row conditionally adds its constant modulo `N` and
returns the active-source word and every VBE work field to the clean boundary. -/
theorem fullRowStep_cleanEndpoint (n N : Nat)
    (constant x : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) (accumulator : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hconstant : constant.val < N) (haccumulator : accumulator < N) :
    fullRowStep n N constant bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          n N x accumulator) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanState n N x
        ((accumulator +
          (if x.val.testBit bitA.val && x.val.testBit bitB.val then
            constant.val else 0)) % N) := by
  let selected : PlainAdder.Word n :=
    if x.val.testBit bitA.val && x.val.testBit bitB.val then constant else 0
  let accumulatorWord : PlainAdder.Word n :=
    (accumulator : PlainAdder.Word n)
  let result :=
    ((accumulator + selected.val) % N)
  let s0 := MAU.Multiplication.Accumulate.VBECircuit.cleanState
    n N x accumulator
  let s1 := MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
    selected (N : PlainAdder.Word n)
    (accumulator : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s2 := MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
    selected (N : PlainAdder.Word n)
    (result : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s3 := MAU.Multiplication.Accumulate.VBECircuit.cleanState
    n N x result
  have hselectedLt : selected.val < N := by
    cases hcontrols :
        (x.val.testBit bitA.val && x.val.testBit bitB.val) <;>
      simp [selected, hcontrols, hconstant, hNpos]
  have haccumulatorPow : accumulator < 2 ^ n :=
    haccumulator.trans hN
  have haccumulatorWordVal : accumulatorWord.val = accumulator :=
    ZMod.val_natCast_of_lt haccumulatorPow
  have htarget :
      MAU.Addition.VBECircuit.widenWord n accumulatorWord =
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) := by
    simpa [accumulatorWord] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        n accumulator haccumulatorPow
  have hresultLt : result < N := Nat.mod_lt _ hNpos
  have hresultPow : result < 2 ^ n := hresultLt.trans hN
  have hs1 : loadStep n constant bitA bitB hne s0 = s1 := by
    simpa [s0, s1,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState, selected] using
      loadStep_cleanEndpoint n constant x bitA bitB hne
        (N : PlainAdder.Word n)
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) false
  have hmod := MAU.Addition.VBECircuit.modularAddStep_cleanEndpoint
    n N selected accumulatorWord hNpos hN hselectedLt
      (by simpa only [haccumulatorWordVal] using haccumulator)
  have hs2 :
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep n N s1 =
        s2 := by
    apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv n).injective
    change
      (x, MAU.Addition.VBECircuit.modularAddStep n N
        (MAU.Addition.VBECircuit.sourceSwapCleanState n selected
          (N : PlainAdder.Word n)
          (accumulator : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) false)) =
      (x, MAU.Addition.VBECircuit.sourceSwapCleanState n selected
        (N : PlainAdder.Word n)
        (result : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) false)
    have hresultWord :
        ((selected.val + accumulatorWord.val) % N :
            PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) =
          (result : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) := by
      simp [result, haccumulatorWordVal, Nat.add_comm]
    simpa [htarget, hresultWord] using
      congrArg (fun arithmetic => (x, arithmetic)) hmod
  have hloadResult : loadStep n constant bitA bitB hne s3 = s2 := by
    have h := loadStep_cleanEndpoint n constant x bitA bitB hne
      (N : PlainAdder.Word n)
      (result : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) false
    have hresultTarget :
        MAU.Addition.VBECircuit.widenWord n
            (result : PlainAdder.Word n) =
          (result : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) := by
      exact
        MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
          n result hresultPow
    simpa [s2, s3,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState, selected,
      hresultTarget] using h
  have hs3 : unloadStep n constant bitA bitB hne s2 = s3 := by
    have hinverse := unloadStep_after_loadStep
      n constant bitA bitB hne s3
    rw [hloadResult] at hinverse
    exact hinverse
  rw [fullRowStep_eq_composition, hs1, hs2, hs3]
  cases hbitA : x.val.testBit bitA.val <;>
    cases hbitB : x.val.testBit bitB.val <;>
    simp [s3, result, selected, hbitA, hbitB]

/-! ### Native Toffoli projection of the full-layout row -/

theorem loadProgram_toffoli_count_eq (n : Nat)
    (constant : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (loadProgram n constant bitA bitB hne).eventCost =
      (EncodedBit.Word.constantOneIndices
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length := by
  unfold loadProgram
  exact doubleControlledXorConstantProgram_toffoli_count_eq _ _ _ _ _ _ _

theorem unloadProgram_toffoli_count_eq (n : Nat)
    (constant : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (unloadProgram n constant bitA bitB hne).eventCost =
      (EncodedBit.Word.constantOneIndices
        (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length := by
  unfold unloadProgram
  exact doubleControlledXorConstantUnloadProgram_toffoli_count_eq _ _ _ _ _ _ _

theorem liftedModularAddProgram_toffoli_count_eq (n N : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddProgram
          n N).eventCost = 30 * n := by
  have hcost :
      (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddProgram
          n N).eventCost =
        (MAU.Addition.VBECircuit.modularAddProgram n N).eventCost := by
    exact UnitaryCircuit.prodRight_eventCost
      (m := (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width)
      (MAU.Addition.VBECircuit.modularAddProgram n N)
  rw [hcost]
  exact MAU.Addition.VBECircuit.modularAddProgram_toffoli_count_eq n N

@[simp] theorem liftArithmeticGate_toffoliMultiplicity (n : Nat)
    (gate : EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n)) :
    EncodedBit.GateSpec.toffoliMultiplicity
        (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate n gate) =
      EncodedBit.GateSpec.toffoliMultiplicity gate := by
  cases gate <;> rfl

private theorem map_liftArithmeticGate_toffoliMultiplicity_sum (n : Nat) :
    ∀ gates : List
        (EncodedBit.GateSpec (MAU.Addition.VBECircuit.encoding n)),
      (((gates.map
          (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate n)).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum) =
        (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum
  | [] => rfl
  | gate :: rest => by
      simp only [List.map_cons, List.sum_cons,
        liftArithmeticGate_toffoliMultiplicity,
        map_liftArithmeticGate_toffoliMultiplicity_sum n rest]

theorem fullLayoutLiftedModularAddGates_toffoliMultiplicity_sum
    (n N : Nat) :
    ((MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates n N).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 30 * n := by
  unfold MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
  rw [map_liftArithmeticGate_toffoliMultiplicity_sum]
  exact MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum n N

/-- Exact native Toffoli count of one complete full-layout table row. -/
def fullRowToffoliCount (n : Nat) (constant : PlainAdder.Word n) : Nat :=
  30 * n +
    2 * (EncodedBit.Word.constantOneIndices
      (MAU.Addition.VBECircuit.controlledConstantLabel n constant)).length

theorem fullRowProgram_toffoli_count_eq (n N : Nat)
    (constant : PlainAdder.Word n) (bitA bitB : Fin n)
    (hne : bitA ≠ bitB) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (fullRowProgram n N constant bitA bitB hne).eventCost =
      fullRowToffoliCount n constant := by
  rw [fullRowProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  simp only [fullRowGates, List.map_append, List.sum_append]
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    show EncodedBit.GateSpec.programList
        (loadGates n constant bitA bitB hne) =
      loadProgram n constant bitA bitB hne from rfl,
    loadProgram_toffoli_count_eq]
  rw [fullLayoutLiftedModularAddGates_toffoliMultiplicity_sum]
  rw [← EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    show EncodedBit.GateSpec.programList
        (unloadGates n constant bitA bitB hne) =
      unloadProgram n constant bitA bitB hne from rfl,
    unloadProgram_toffoli_count_eq]
  simp [fullRowToffoliCount]
  omega

/-- One complete full-layout row uses at most `32*n+2` Toffolis. -/
theorem fullRowToffoliCount_le (n : Nat) (constant : PlainAdder.Word n) :
    fullRowToffoliCount n constant ≤ 32 * n + 2 := by
  have hset := EncodedBit.Word.constantOneIndices_length_le
    (MAU.Addition.VBECircuit.controlledConstantLabel n constant)
  simp only [MAU.Addition.VBECircuit.AdderWidth] at hset
  unfold fullRowToffoliCount
  omega

/-! ### One-add QROM lookup window -/

/-- Bitwise-xor correction which turns two singly controlled loads and one
doubly controlled load into a four-way lookup with zero at address `00`. -/
def xorCorrectionLabel (n : Nat)
    (first second third : PlainAdder.Word n) :
    Fin (2 ^ MAU.Addition.VBECircuit.AdderWidth n) :=
  let firstLabel := MAU.Addition.VBECircuit.controlledConstantLabel n first
  let secondLabel := MAU.Addition.VBECircuit.controlledConstantLabel n second
  let thirdLabel := MAU.Addition.VBECircuit.controlledConstantLabel n third
  ⟨firstLabel.val ^^^ secondLabel.val ^^^ thirdLabel.val,
    Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow firstLabel.isLt secondLabel.isLt)
      thirdLabel.isLt⟩

theorem xorCorrectionLabel_testBit (n : Nat)
    (first second third : PlainAdder.Word n)
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth n)) :
    (xorCorrectionLabel n first second third).val.testBit bit.val =
      ((MAU.Addition.VBECircuit.controlledConstantLabel n first).val.testBit
          bit.val ^^
        (MAU.Addition.VBECircuit.controlledConstantLabel n second).val.testBit
          bit.val ^^
        (MAU.Addition.VBECircuit.controlledConstantLabel n third).val.testBit
          bit.val) := by
  simp [xorCorrectionLabel, Nat.testBit_xor]

/-- Boolean Möbius identity underlying the three-term QROM lookup. -/
theorem mobiusLookupBit (addressA addressB first second third : Bool) :
    ((addressA && first) ^^
        (addressB && second) ^^
        (addressA && addressB && (first ^^ second ^^ third))) =
      if addressA then
        if addressB then third else first
      else if addressB then second else false := by
  cases addressA <;> cases addressB <;>
    cases first <;> cases second <;> cases third <;> rfl

/-- Physical QROM load: two CNOT-only linear terms followed by the nonlinear
Toffoli correction. -/
def lookupLoadGates (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  EncodedBit.Word.controlledXorConstantGates
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
      (MAU.Addition.VBECircuit.controlledConstantLabel n first)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA) ++
    EncodedBit.Word.controlledXorConstantGates
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
      (MAU.Addition.VBECircuit.controlledConstantLabel n second)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB) ++
    EncodedBit.Word.doubleControlledXorConstantGates
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
      (xorCorrectionLabel n first second third)
      (sourceControls_ne n bitA bitB hne)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB)

/-- Folded action of the three-term QROM load. -/
def lookupLoadStep (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n := fun state =>
  EncodedBit.Word.doubleControlledXorConstantStep
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (xorCorrectionLabel n first second third)
    (sourceControls_ne n bitA bitB hne)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)
    (EncodedBit.Word.controlledXorConstantStep
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
      (MAU.Addition.VBECircuit.controlledConstantLabel n second)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB)
      (EncodedBit.Word.controlledXorConstantStep
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
        (MAU.Addition.VBECircuit.controlledConstantLabel n first)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA) state))

theorem lookupLoadStep_eq_gateList (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) (state : Registers n) :
    EncodedBit.GateSpec.stepList
        (lookupLoadGates n first second third bitA bitB hne) state =
      lookupLoadStep n first second third bitA bitB hne state := by
  simp only [lookupLoadGates, EncodedBit.GateSpec.stepList_append]
  rfl

/-- The lookup load preserves every readout outside the active-source word. -/
theorem lookupLoadStep_get_observed_of_target_ne (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB)
    (observed : EncodedBit (encoding n))
    (htargetObserved : ∀ sourceBit,
      ((MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
          sourceBit).wire ≠ observed.wire)
    (state : Registers n) :
    observed.get (lookupLoadStep n first second third bitA bitB hne state) =
      observed.get state := by
  unfold lookupLoadStep
  rw [EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
    _ _ _ _ _ _ _ observed htargetObserved]
  rw [EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
    _ _ _ _ observed htargetObserved]
  rw [EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
    _ _ _ _ observed htargetObserved]

/-- Exact target-bit action of the three-term QROM lookup on an arbitrary
full-layout basis label. -/
theorem lookupLoadStep_get_target (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB)
    (sourceBit : Fin (MAU.Addition.VBECircuit.AdderWidth n))
    (state : Registers n) :
    ((MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
        sourceBit).get
        (lookupLoadStep n first second third bitA bitB hne state) =
      (((MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
          sourceBit).get state ^^
        ((MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA).get
            state &&
          (MAU.Addition.VBECircuit.controlledConstantLabel n first).val.testBit
            sourceBit.val) ^^
        ((MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB).get
            state &&
          (MAU.Addition.VBECircuit.controlledConstantLabel n second).val.testBit
            sourceBit.val) ^^
        ((MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA).get
            state &&
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB).get
            state &&
          (xorCorrectionLabel n first second third).val.testBit
            sourceBit.val)) := by
  let controlA :=
    MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA
  let controlB :=
    MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB
  let target := MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n
  let firstLabel := MAU.Addition.VBECircuit.controlledConstantLabel n first
  let secondLabel := MAU.Addition.VBECircuit.controlledConstantLabel n second
  let correction := xorCorrectionLabel n first second third
  let afterA := EncodedBit.Word.controlledXorConstantStep
    controlA target firstLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA) state
  let afterB := EncodedBit.Word.controlledXorConstantStep
    controlB target secondLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB) afterA
  have htargetPairwise : ∀ other, other ≠ sourceBit →
      (target.bit other).wire ≠ (target.bit sourceBit).wire := by
    exact fun other hother =>
      MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
        n other sourceBit hother
  have hAafterA : controlA.get afterA = controlA.get state := by
    exact EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
      controlA target firstLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA) controlA
      (fun bit => Ne.symm
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA bit)) state
  have hBafterA : controlB.get afterA = controlB.get state := by
    exact EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
      controlA target firstLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA) controlB
      (fun bit => Ne.symm
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB bit)) state
  have hAafterB : controlA.get afterB = controlA.get afterA := by
    exact EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
      controlB target secondLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB) controlA
      (fun bit => Ne.symm
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA bit)) afterA
  have hBafterB : controlB.get afterB = controlB.get afterA := by
    exact EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
      controlB target secondLabel
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB) controlB
      (fun bit => Ne.symm
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB bit)) afterA
  have hdouble :=
    EncodedBit.Word.doubleControlledXorConstantStep_get_target
      controlA controlB target correction
      (sourceControls_ne n bitA bitB hne)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitA)
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
        n bitB)
      sourceBit htargetPairwise afterB
  have hsecond := EncodedBit.Word.controlledXorConstantStep_get_target
    controlB target secondLabel
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB) sourceBit htargetPairwise afterA
  have hfirst := EncodedBit.Word.controlledXorConstantStep_get_target
    controlA target firstLabel
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA) sourceBit htargetPairwise state
  change (target.bit sourceBit).get
      (EncodedBit.Word.doubleControlledXorConstantStep controlA controlB
        target correction (sourceControls_ne n bitA bitB hne)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitA)
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n bitB) afterB) = _
  rw [hdouble, hAafterB, hBafterB, hAafterA, hBafterA, hsecond,
    hBafterA, hfirst]

/-- Program view of the same QROM lookup gate list. -/
def lookupLoadProgram (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.GateSpec.programList
    (lookupLoadGates n first second third bitA bitB hne)

theorem lookupLoad_realizes (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit.Realizes (encoding n)
      (lookupLoadProgram n first second third bitA bitB hne)
      (lookupLoadStep n first second third bitA bitB hne) := by
  apply UnitaryCircuit.Realizes.congrStep (EncodedBit.GateSpec.realizesList _)
  exact lookupLoadStep_eq_gateList n first second third bitA bitB hne

/-- Classical constant selected by the two-bit QROM address. -/
def selectedLookupConstant {n : Nat} (addressA addressB : Bool)
    (first second third : PlainAdder.Word n) : PlainAdder.Word n :=
  if addressA then
    if addressB then third else first
  else if addressB then second else 0

/-- Starting from a zero active-source word, the three-term QROM loads exactly
the selected table constant and preserves every other full-layout field. -/
theorem lookupLoadStep_cleanEndpoint (n : Nat)
    (first second third x : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n))
    (flag : Bool) :
    lookupLoadStep n first second third bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.workspaceState
          n x 0 parked target flag) =
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
        (selectedLookupConstant
          (x.val.testBit bitA.val) (x.val.testBit bitB.val)
          first second third)
        parked target flag := by
  let input := MAU.Multiplication.Accumulate.VBECircuit.workspaceState
    n x 0 parked target flag
  let selected := selectedLookupConstant
    (x.val.testBit bitA.val) (x.val.testBit bitB.val) first second third
  have hactive :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord n selected := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro sourceBit
    rw [← MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get]
    have hread := lookupLoadStep_get_target
      n first second third bitA bitB hne sourceBit input
    rw [show
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n).bit
          sourceBit =
        MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit n sourceBit
      from rfl] at hread
    rw [MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get] at hread
    have hfirst := MAU.Addition.VBECircuit.controlledConstantLabel_testBit
      n first sourceBit
    have hsecond := MAU.Addition.VBECircuit.controlledConstantLabel_testBit
      n second sourceBit
    have hthird := MAU.Addition.VBECircuit.controlledConstantLabel_testBit
      n third sourceBit
    have hcorrection := xorCorrectionLabel_testBit
      n first second third sourceBit
    have hzeroBit :
        (MAU.Addition.VBECircuit.widenWord n
          (0 : PlainAdder.Word n)).val.testBit sourceBit.val = false := by
      rw [MAU.Addition.VBECircuit.widenWord_val]
      simp
    have hinputActive :
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit n
          sourceBit).get input = false := by
      simp [input,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState]
    rw [hinputActive, Bool.false_xor, hcorrection, mobiusLookupBit] at hread
    cases hbitA : x.val.testBit bitA.val <;>
      cases hbitB : x.val.testBit bitB.val <;>
      simpa [input,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState, selected,
        selectedLookupConstant, hbitA, hbitB, hfirst, hsecond, hthird,
        hzeroBit] using hread
  have hmultiplicand :
      (lookupLoadStep n first second third bitA bitB hne input).multiplicand =
        x := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro observedBit
    rw [← MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get]
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n observedBit)
      (fun sourceBit => Ne.symm
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
          n observedBit sourceBit)) input
    simpa [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using hread
  have htarget :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.target =
        target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro targetBit
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.targetBit n targetBit)
      (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
        n (MAU.Addition.VBECircuit.targetBit n targetBit)
        (fun sourceBit =>
          MAU.Addition.VBECircuit.activeSource_target_ne
            n sourceBit targetBit)) input
    simpa [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hcarry :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.carry =
        false := by
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
        (MAU.Addition.VBECircuit.carryBit n))
      (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
        n (MAU.Addition.VBECircuit.carryBit n)
        (MAU.Addition.VBECircuit.activeSource_carry_ne n)) input
    simpa [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hparked :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.parkedSource =
        parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro parkedBit
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
        (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit))
      (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
        n (MAU.Addition.VBECircuit.parkedSourceBit n parkedBit)
        (fun sourceBit =>
          MAU.Addition.VBECircuit.activeSource_parked_ne
            n sourceBit parkedBit)) input
    simpa [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hwork :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth n) := by
    change
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.carryWork =
        0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    rw [← MAU.Addition.VBECircuit.carryWorkBit_get n workBit]
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
        (MAU.Addition.VBECircuit.carryWorkBit n workBit))
      (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
        n (MAU.Addition.VBECircuit.carryWorkBit n workBit)
        (fun sourceBit =>
          MAU.Addition.VBECircuit.activeSource_carryWork_ne
            n sourceBit workBit)) input
    have hread' :
        (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            (lookupLoadStep n first second third bitA bitB hne input).arithmetic =
          (MAU.Addition.VBECircuit.carryWorkBit n workBit).get
            input.arithmetic := by
      simpa using hread
    rw [hread', MAU.Addition.VBECircuit.carryWorkBit_get]
    simp [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic.reductionFlag =
        flag := by
    have hread := lookupLoadStep_get_observed_of_target_ne
      n first second third bitA bitB hne
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit n
        (MAU.Addition.VBECircuit.reductionFlagBit n))
      (MAU.Multiplication.Accumulate.VBECircuit.activeSource_liftArithmetic_ne
        n (MAU.Addition.VBECircuit.reductionFlagBit n)
        (fun sourceBit => Ne.symm
          (MAU.Addition.VBECircuit.reductionFlag_activeSource_ne
            n sourceBit))) input
    simpa [input,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  change lookupLoadStep n first second third bitA bitB hne input = _
  apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv n).injective
  change
    ((lookupLoadStep n first second third bitA bitB hne input).multiplicand,
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic) =
    (x, MAU.Addition.VBECircuit.sourceSwapCleanState n selected parked target
      flag)
  rw [hmultiplicand]
  congr 1
  rcases harithmetic :
      (lookupLoadStep n first second third bitA bitB hne input).arithmetic with
    ⟨active, target', carry, parked', work, flag'⟩
  simp only [harithmetic] at hactive htarget hcarry hparked hwork hflag ⊢
  subst_vars
  rfl

/-- Exact reverse of the QROM lookup-load list. -/
def lookupUnloadGates (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (lookupLoadGates n first second third bitA bitB hne).reverse

/-- Folded action of the reverse QROM lookup list. -/
def lookupUnloadStep (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n :=
  EncodedBit.GateSpec.stepList
    (lookupUnloadGates n first second third bitA bitB hne)

theorem lookupUnloadStep_after_lookupLoadStep (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) (state : Registers n) :
    lookupUnloadStep n first second third bitA bitB hne
        (lookupLoadStep n first second third bitA bitB hne state) = state := by
  rw [← lookupLoadStep_eq_gateList]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (lookupLoadGates n first second third bitA bitB hne) state

/-- One exact two-bit QROM window performs one lookup, one modular addition,
and the reverse lookup. -/
def qromWindowGates (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    List (EncodedBit.GateSpec (encoding n)) :=
  lookupLoadGates n first second third bitA bitB hne ++
    MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates n N ++
    lookupUnloadGates n first second third bitA bitB hne

/-- Program compiled from the one-add QROM window gate list. -/
def qromWindowProgram (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit (Qubits (encoding n).width) :=
  EncodedBit.GateSpec.programList
    (qromWindowGates n N first second third bitA bitB hne)

/-- Folded basis action of one one-add QROM window. -/
def qromWindowStep (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    Registers n → Registers n :=
  EncodedBit.GateSpec.stepList
    (qromWindowGates n N first second third bitA bitB hne)

theorem qromWindowStep_eq_composition (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) (state : Registers n) :
    qromWindowStep n N first second third bitA bitB hne state =
      lookupUnloadStep n first second third bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep n N
          (lookupLoadStep n first second third bitA bitB hne state)) := by
  simp only [qromWindowStep, qromWindowGates,
    EncodedBit.GateSpec.stepList_append]
  rw [lookupLoadStep_eq_gateList,
    MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep_eq_gateList]
  rfl

theorem qromWindow_realizes (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    UnitaryCircuit.Realizes (encoding n)
      (qromWindowProgram n N first second third bitA bitB hne)
      (qromWindowStep n N first second third bitA bitB hne) :=
  EncodedBit.GateSpec.realizesList _

/-- A one-add QROM window adds the selected table row modulo `N` and returns
the lookup word and all VBE work fields to zero. -/
theorem qromWindowStep_cleanEndpoint (n N : Nat)
    (first second third x : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) (accumulator : Nat)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (hfirst : first.val < N) (hsecond : second.val < N)
    (hthird : third.val < N) (haccumulator : accumulator < N) :
    qromWindowStep n N first second third bitA bitB hne
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          n N x accumulator) =
      MAU.Multiplication.Accumulate.VBECircuit.cleanState n N x
        ((accumulator +
          (selectedLookupConstant
            (x.val.testBit bitA.val) (x.val.testBit bitB.val)
            first second third).val) % N) := by
  let selected := selectedLookupConstant
    (x.val.testBit bitA.val) (x.val.testBit bitB.val) first second third
  let accumulatorWord : PlainAdder.Word n :=
    (accumulator : PlainAdder.Word n)
  let result := (accumulator + selected.val) % N
  let s0 := MAU.Multiplication.Accumulate.VBECircuit.cleanState
    n N x accumulator
  let s1 := MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
    selected (N : PlainAdder.Word n)
    (accumulator : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s2 := MAU.Multiplication.Accumulate.VBECircuit.workspaceState n x
    selected (N : PlainAdder.Word n)
    (result : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth n)) false
  let s3 := MAU.Multiplication.Accumulate.VBECircuit.cleanState n N x result
  have hselectedLt : selected.val < N := by
    cases hbitA : x.val.testBit bitA.val <;>
      cases hbitB : x.val.testBit bitB.val <;>
      simp [selected, selectedLookupConstant, hbitA, hbitB,
        hfirst, hsecond, hthird, hNpos]
  have haccumulatorPow : accumulator < 2 ^ n := haccumulator.trans hN
  have haccumulatorWordVal : accumulatorWord.val = accumulator :=
    ZMod.val_natCast_of_lt haccumulatorPow
  have htarget :
      MAU.Addition.VBECircuit.widenWord n accumulatorWord =
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) := by
    simpa [accumulatorWord] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        n accumulator haccumulatorPow
  have hresultLt : result < N := Nat.mod_lt _ hNpos
  have hresultPow : result < 2 ^ n := hresultLt.trans hN
  have hs1 :
      lookupLoadStep n first second third bitA bitB hne s0 = s1 := by
    simpa [s0, s1,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState, selected] using
      lookupLoadStep_cleanEndpoint n first second third x bitA bitB hne
        (N : PlainAdder.Word n)
        (accumulator : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) false
  have hmod := MAU.Addition.VBECircuit.modularAddStep_cleanEndpoint
    n N selected accumulatorWord hNpos hN hselectedLt
      (by simpa only [haccumulatorWordVal] using haccumulator)
  have hs2 :
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep n N s1 =
        s2 := by
    apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv n).injective
    change
      (x, MAU.Addition.VBECircuit.modularAddStep n N
        (MAU.Addition.VBECircuit.sourceSwapCleanState n selected
          (N : PlainAdder.Word n)
          (accumulator : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) false)) =
      (x, MAU.Addition.VBECircuit.sourceSwapCleanState n selected
        (N : PlainAdder.Word n)
        (result : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth n)) false)
    have hresultWord :
        ((selected.val + accumulatorWord.val) % N :
            PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) =
          (result : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) := by
      simp [result, haccumulatorWordVal, Nat.add_comm]
    simpa [htarget, hresultWord] using
      congrArg (fun arithmetic => (x, arithmetic)) hmod
  have hloadResult :
      lookupLoadStep n first second third bitA bitB hne s3 = s2 := by
    have h := lookupLoadStep_cleanEndpoint
      n first second third x bitA bitB hne (N : PlainAdder.Word n)
      (result : PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth n)) false
    have hresultTarget :
        MAU.Addition.VBECircuit.widenWord n
            (result : PlainAdder.Word n) =
          (result : PlainAdder.Word
            (MAU.Addition.VBECircuit.AdderWidth n)) :=
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        n result hresultPow
    simpa [s2, s3,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState, selected,
      hresultTarget] using h
  have hs3 :
      lookupUnloadStep n first second third bitA bitB hne s2 = s3 := by
    have hinverse := lookupUnloadStep_after_lookupLoadStep
      n first second third bitA bitB hne s3
    rw [hloadResult] at hinverse
    exact hinverse
  rw [qromWindowStep_eq_composition, hs1, hs2, hs3]

/-! #### Width-only primitive bound of one QROM window -/

/-- The three-term lookup emits at most one primitive per active-source bit
for each of its two linear loads and its nonlinear correction. -/
theorem lookupLoadGates_length_le (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    (lookupLoadGates n first second third bitA bitB hne).length ≤
      3 * (n + 1) := by
  have hfirst := EncodedBit.Word.controlledXorConstantGates_length_le_width
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitA)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n first)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitA)
  have hsecond := EncodedBit.Word.controlledXorConstantGates_length_le_width
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit n bitB)
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord n)
    (MAU.Addition.VBECircuit.controlledConstantLabel n second)
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      n bitB)
  have hcorrection := EncodedBit.Word.constantOneIndices_length_le
    (xorCorrectionLabel n first second third)
  simp only [lookupLoadGates, List.length_append,
    EncodedBit.Word.controlledXorConstantGates_length,
    EncodedBit.Word.doubleControlledXorConstantGates,
    List.length_map, MAU.Addition.VBECircuit.AdderWidth] at hfirst hsecond hcorrection ⊢
  omega

/-- Reversing the lookup preserves its width-only primitive bound. -/
theorem lookupUnloadGates_length_le (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    (lookupUnloadGates n first second third bitA bitB hne).length ≤
      3 * (n + 1) := by
  simpa only [lookupUnloadGates, List.length_reverse] using
    lookupLoadGates_length_le n first second third bitA bitB hne

/-- One lookup/add/unlookup window has a linear primitive bound. -/
theorem qromWindowGates_length_le (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    (qromWindowGates n N first second third bitA bitB hne).length ≤
      54 * n + 51 := by
  have hload := lookupLoadGates_length_le
    n first second third bitA bitB hne
  have hunload := lookupUnloadGates_length_le
    n first second third bitA bitB hne
  have hadd := MAU.Addition.VBECircuit.modularAddGates_length_le n N
  have hlift :
      (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
        n N).length ≤ 48 * n + 45 := by
    simpa [MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates]
      using hadd
  simp only [qromWindowGates, List.length_append]
  omega

/-! #### Native Toffoli projection of one QROM window -/

theorem lookupLoadGates_toffoliMultiplicity_sum (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    ((lookupLoadGates n first second third bitA bitB hne).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (EncodedBit.Word.constantOneIndices
        (xorCorrectionLabel n first second third)).length := by
  simp only [lookupLoadGates, List.map_append, List.sum_append]
  rw [EncodedBit.Word.controlledXorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.controlledXorConstantGates_toffoliMultiplicity_sum]
  simp only [zero_add]
  unfold EncodedBit.Word.doubleControlledXorConstantGates
  generalize EncodedBit.Word.constantOneIndices
      (xorCorrectionLabel n first second third) = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      rw [List.map_map] at ih
      simp [ih, EncodedBit.GateSpec.toffoliMultiplicity_toffoli,
        Nat.add_comm]

theorem lookupUnloadGates_toffoliMultiplicity_sum (n : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    ((lookupUnloadGates n first second third bitA bitB hne).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (EncodedBit.Word.constantOneIndices
        (xorCorrectionLabel n first second third)).length := by
  simp [lookupUnloadGates, List.map_reverse, List.sum_reverse,
    lookupLoadGates_toffoliMultiplicity_sum]

/-- Exact native Toffoli coordinate of one one-add QROM window. -/
def qromWindowToffoliCount (n : Nat)
    (first second third : PlainAdder.Word n) : Nat :=
  30 * n +
    2 * (EncodedBit.Word.constantOneIndices
      (xorCorrectionLabel n first second third)).length

theorem qromWindowProgram_toffoli_count_eq (n N : Nat)
    (first second third : PlainAdder.Word n)
    (bitA bitB : Fin n) (hne : bitA ≠ bitB) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (qromWindowProgram n N first second third bitA bitB hne).eventCost =
      qromWindowToffoliCount n first second third := by
  rw [qromWindowProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  simp only [qromWindowGates, List.map_append, List.sum_append]
  rw [lookupLoadGates_toffoliMultiplicity_sum,
    fullLayoutLiftedModularAddGates_toffoliMultiplicity_sum,
    lookupUnloadGates_toffoliMultiplicity_sum]
  simp [qromWindowToffoliCount]
  omega

/-- One exact one-add QROM window uses at most `32*n+2` Toffolis. -/
theorem qromWindowToffoliCount_le (n : Nat)
    (first second third : PlainAdder.Word n) :
    qromWindowToffoliCount n first second third ≤ 32 * n + 2 := by
  have hset := EncodedBit.Word.constantOneIndices_length_le
    (xorCorrectionLabel n first second third)
  simp only [MAU.Addition.VBECircuit.AdderWidth] at hset
  unfold qromWindowToffoliCount
  omega

end FullLayout

end

end MAU.Multiplication.Windowed
end QuantumAlg

end
