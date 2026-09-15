/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import Mathlib.GroupTheory.Perm.Sign

/-!
# Clean one-hot compilation of finite basis permutations

A finite public permutation is represented as a permutation of one-hot wires.
Mathlib supplies a transposition factorization, and every controlled wire
transposition is the repository's three-Toffoli controlled swap.  The resulting
program therefore contains only X/CNOT/Toffoli primitives and restores the
one-hot tail to canonical form.
-/

section

namespace QuantumAlg
namespace OneHotPermutation

noncomputable section

/-- Canonical wire occupied by a finite semantic value. -/
def wireOf {α : Type} [Fintype α] (x : α) : Fin (Fintype.card α) :=
  Fintype.equivFin α x

/-- Raw one-hot label occupying one selected wire. -/
def rawOneHotLabel {n : Nat} (wire : Fin n) : Fin (2 ^ n) :=
  ⟨2 ^ (WireAddress.bitIndex wire).val,
    Nat.pow_lt_pow_right one_lt_two (WireAddress.bitIndex wire).isLt⟩

/-- Computational-basis label with exactly the semantic value's wire set. -/
def oneHotLabel {α : Type} [Fintype α] (x : α) :
    Fin (2 ^ Fintype.card α) :=
  rawOneHotLabel (wireOf x)

/-- Distinct finite values have distinct one-hot labels. -/
theorem oneHotLabel_injective {α : Type} [Fintype α] :
    Function.Injective (oneHotLabel (α := α)) := by
  intro x y h
  apply (Fintype.equivFin α).injective
  apply WireAddress.bitIndex_injective
  apply Fin.ext
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  exact congrArg Fin.val h

/-- Faithful semantic encoding of a finite type by one-hot basis labels. -/
def oneHotEncoding (α : Type) [Fintype α] : BinaryLabelEncoding α where
  width := Fintype.card α
  encode := oneHotLabel
  encode_injective := oneHotLabel_injective

/-- A raw one-hot label reads true exactly at its occupied wire. -/
@[simp] theorem rawOneHotLabel_testBit {n : Nat} (occupied wire : Fin n) :
    (rawOneHotLabel occupied).val.testBit
        (WireAddress.bitIndex wire).val = decide (wire = occupied) := by
  rw [show (rawOneHotLabel occupied).val =
    2 ^ (WireAddress.bitIndex occupied).val by rfl]
  rw [Nat.testBit_two_pow, decide_eq_decide]
  constructor
  · intro h
    exact (WireAddress.bitIndex_injective (Fin.ext h)).symm
  · rintro rfl
    rfl

/-- A one-hot label reads true exactly at its occupied wire. -/
@[simp] theorem oneHotLabel_testBit {α : Type} [Fintype α]
    (x : α) (wire : Fin (Fintype.card α)) :
    (oneHotLabel x).val.testBit (WireAddress.bitIndex wire).val =
      decide (wire = wireOf x) := by
  simp [oneHotLabel]

/-- Finite binary labels are equal when every addressed wire has the same
readout. -/
theorem finLabel_eq_of_wire_testBit_eq {n : Nat}
    {left right : Fin (2 ^ n)}
    (h : ∀ wire : Fin n,
      left.val.testBit (WireAddress.bitIndex wire).val =
        right.val.testBit (WireAddress.bitIndex wire).val) :
    left = right := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < n
  · let wire := WireAddress.littleEndianWire ⟨bit, hbit⟩
    simpa [wire] using h wire
  · have hnbit : n ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ n ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hnbit
    rw [Nat.testBit_eq_false_of_lt (left.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (right.isLt.trans_le hpow)]

/-- Conjugate a public semantic permutation to its one-hot wire permutation. -/
def wirePermutation {α : Type} [Fintype α] (perm : Equiv.Perm α) :
    Equiv.Perm (Fin (Fintype.card α)) :=
  (Fintype.equivFin α).permCongr perm

@[simp] theorem wirePermutation_wireOf {α : Type} [Fintype α]
    (perm : Equiv.Perm α) (x : α) :
    wirePermutation perm (wireOf x) = wireOf (perm x) := by
  simp [wirePermutation, wireOf, Equiv.permCongr]

/-- A transposition with its distinct wire endpoints exposed. -/
structure SwapSpec (n : Nat) where
  /-- First wire. -/
  left : Fin n
  /-- Second wire. -/
  right : Fin n
  /-- A transposition never swaps a wire with itself. -/
  ne : left ≠ right

namespace SwapSpec

/-- Permutation represented by one swap specification. -/
def perm {n : Nat} (spec : SwapSpec n) : Equiv.Perm (Fin n) :=
  Equiv.swap spec.left spec.right

/-- Reading the left wire after a swap is the former right-wire readout. -/
@[simp] theorem left_eq_perm_decide {n : Nat} (spec : SwapSpec n)
    (occupied : Fin n) :
    decide (spec.left = spec.perm occupied) =
      decide (spec.right = occupied) := by
  by_cases hleft : occupied = spec.left
  · subst occupied
    simp [perm, spec.ne, Ne.symm spec.ne]
  · by_cases hright : occupied = spec.right
    · subst occupied
      simp [perm]
    · simp [perm, Equiv.swap_apply_def, hleft, hright,
        Ne.symm hleft, Ne.symm hright]

/-- Reading the right wire after a swap is the former left-wire readout. -/
@[simp] theorem right_eq_perm_decide {n : Nat} (spec : SwapSpec n)
    (occupied : Fin n) :
    decide (spec.right = spec.perm occupied) =
      decide (spec.left = occupied) := by
  by_cases hleft : occupied = spec.left
  · subst occupied
    simp [perm]
  · by_cases hright : occupied = spec.right
    · subst occupied
      simp [perm, spec.ne, Ne.symm spec.ne]
    · simp [perm, Equiv.swap_apply_def, hleft, hright,
        Ne.symm hleft, Ne.symm hright]

/-- Every wire outside a transposition keeps its former readout. -/
@[simp] theorem other_eq_perm_decide {n : Nat} (spec : SwapSpec n)
    (observed occupied : Fin n) (hleft : observed ≠ spec.left)
    (hright : observed ≠ spec.right) :
    decide (observed = spec.perm occupied) =
      decide (observed = occupied) := by
  by_cases hoccupiedLeft : occupied = spec.left
  · subst occupied
    simp [perm, hleft, hright]
  · by_cases hoccupiedRight : occupied = spec.right
    · subst occupied
      simp [perm, hleft, hright]
    · simp [perm, Equiv.swap_apply_def, hoccupiedLeft, hoccupiedRight]

end SwapSpec

/-- Extract explicit endpoints from Mathlib's transposition predicate. -/
noncomputable def swapSpecOfIsSwap {n : Nat} (factor : Equiv.Perm (Fin n))
    (hfactor : factor.IsSwap) : SwapSpec n :=
  Classical.choose (show ∃ spec : SwapSpec n, factor = spec.perm by
    rcases hfactor with ⟨left, right, hne, rfl⟩
    exact ⟨⟨left, right, hne⟩, rfl⟩)

@[simp] theorem swapSpecOfIsSwap_perm {n : Nat}
    (factor : Equiv.Perm (Fin n)) (hfactor : factor.IsSwap) :
    (swapSpecOfIsSwap factor hfactor).perm = factor := by
  exact (Classical.choose_spec
    (show ∃ spec : SwapSpec n, factor = spec.perm by
      rcases hfactor with ⟨left, right, hne, rfl⟩
      exact ⟨⟨left, right, hne⟩, rfl⟩)).symm

/-- Explicit transposition list whose product is the supplied wire
permutation. -/
def factorSpecs {n : Nat} (perm : Equiv.Perm (Fin n)) : List (SwapSpec n) :=
  let factors := (Equiv.Perm.swapFactors perm).val
  factors.attach.map fun factor =>
    swapSpecOfIsSwap factor.val
      ((Equiv.Perm.swapFactors perm).property.2 factor.val factor.property)

theorem factorSpecs_perm_prod {n : Nat} (perm : Equiv.Perm (Fin n)) :
    ((factorSpecs perm).map SwapSpec.perm).prod = perm := by
  simpa [factorSpecs] using (Equiv.Perm.swapFactors perm).property.1

/-- Full product encoding for a control carrier and raw one-hot tail. -/
abbrev controlledEncoding {Control : Type} (controlEncoding : BinaryLabelEncoding Control)
    (n : Nat) : BinaryLabelEncoding (Control × Fin (2 ^ n)) :=
  BinaryLabelEncoding.prod controlEncoding (BinaryLabelEncoding.finIdentity n)

/-- Product encoding of the control carrier and a semantic one-hot value. -/
abbrev controlledOneHotEncoding {Control α : Type}
    (controlEncoding : BinaryLabelEncoding Control) [Fintype α] :
    BinaryLabelEncoding (Control × α) :=
  BinaryLabelEncoding.prod controlEncoding (oneHotEncoding α)

/-- Lift one control-carrier bit before the raw one-hot tail. -/
def liftedControl {Control : Type} {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) (n : Nat) :
    EncodedBit (controlledEncoding controlEncoding n) :=
  BinaryLabelEncoding.prodLeftBit controlEncoding
    (BinaryLabelEncoding.finIdentity n) control

/-- Address one raw one-hot tail wire after the control carrier. -/
def tailBit {Control : Type} (controlEncoding : BinaryLabelEncoding Control)
    {n : Nat} (wire : Fin n) :
    EncodedBit (controlledEncoding controlEncoding n) :=
  BinaryLabelEncoding.prodRightBit controlEncoding
    (BinaryLabelEncoding.finIdentity n)
    (BinaryLabelEncoding.finIdentityBit n wire)

/-- A lifted control bit reads only the control-carrier component. -/
@[simp] theorem liftedControl_get {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) (n : Nat)
    (value : Control × Fin (2 ^ n)) :
    (liftedControl control n).get value = control.get value.1 :=
  rfl

/-- A lifted tail bit reads the addressed raw one-hot label bit. -/
@[simp] theorem tailBit_get {Control : Type}
    (controlEncoding : BinaryLabelEncoding Control) {n : Nat}
    (wire : Fin n) (value : Control × Fin (2 ^ n)) :
    (tailBit controlEncoding wire).get value =
      value.2.val.testBit (WireAddress.bitIndex wire).val :=
  rfl

/-- Flipping a tail bit leaves the complete control carrier unchanged. -/
@[simp] theorem tailBit_flip_fst {Control : Type}
    (controlEncoding : BinaryLabelEncoding Control) {n : Nat}
    (wire : Fin n) (value : Control × Fin (2 ^ n)) :
    ((tailBit controlEncoding wire).flip value).1 = value.1 :=
  rfl

theorem liftedControl_ne_tailBit {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat} (wire : Fin n) :
    (liftedControl control n).wire ≠ (tailBit controlEncoding wire).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp [liftedControl, tailBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hv
  omega

theorem tailBit_ne {Control : Type}
    (controlEncoding : BinaryLabelEncoding Control) {n : Nat}
    {left right : Fin n} (hne : left ≠ right) :
    (tailBit controlEncoding left).wire ≠
      (tailBit controlEncoding right).wire := by
  intro h
  apply hne
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [tailBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit] using hv

/-- Three-Toffoli gate list for one controlled wire transposition. -/
def controlledSwapGatesFor {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat} (spec : SwapSpec n) :
    List (EncodedBit.GateSpec (controlledEncoding controlEncoding n)) :=
  EncodedBit.controlledSwapGates
    (liftedControl control n)
    (tailBit controlEncoding spec.left)
    (tailBit controlEncoding spec.right)
    (liftedControl_ne_tailBit control spec.left)
    (liftedControl_ne_tailBit control spec.right)
    (tailBit_ne controlEncoding spec.ne)

@[simp] theorem controlledSwapGatesFor_length {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat} (spec : SwapSpec n) :
    (controlledSwapGatesFor control spec).length = 3 := by
  rfl

/-- One synthesized transposition moves a canonical one-hot label exactly
when the selected control bit is set. -/
theorem controlledSwapGatesFor_step_rawOneHot {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat} (spec : SwapSpec n)
    (controlValue : Control) (occupied : Fin n) :
    EncodedBit.GateSpec.stepList (controlledSwapGatesFor control spec)
        (controlValue, rawOneHotLabel occupied) =
      (controlValue,
        rawOneHotLabel
          (if control.get controlValue then spec.perm occupied else occupied)) := by
  apply Prod.ext
  · simpa using
      (EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
          (gates := controlledSwapGatesFor control spec)
          (project := Prod.fst)
          (fun gate hgate => by
            simp only [controlledSwapGatesFor,
              EncodedBit.controlledSwapGates, List.mem_cons,
              List.not_mem_nil, or_false] at hgate
            rcases hgate with rfl | rfl | rfl <;>
              simp [EncodedBit.GateSpec.targetFlipPreserves])
          (controlValue, rawOneHotLabel occupied))
  · apply finLabel_eq_of_wire_testBit_eq
    intro observed
    by_cases hleft : observed = spec.left
    · subst observed
      have hread := EncodedBit.controlledSwapStep_get_left
        (liftedControl control n)
        (tailBit controlEncoding spec.left)
        (tailBit controlEncoding spec.right)
        (liftedControl_ne_tailBit control spec.left)
        (liftedControl_ne_tailBit control spec.right)
        (tailBit_ne controlEncoding spec.ne)
        (controlValue, rawOneHotLabel occupied)
      by_cases hcontrol : control.get controlValue <;>
        simpa [controlledSwapGatesFor, EncodedBit.controlledSwapStep,
          hcontrol] using hread
    · by_cases hright : observed = spec.right
      · subst observed
        have hread := EncodedBit.controlledSwapStep_get_right
          (liftedControl control n)
          (tailBit controlEncoding spec.left)
          (tailBit controlEncoding spec.right)
          (liftedControl_ne_tailBit control spec.left)
          (liftedControl_ne_tailBit control spec.right)
          (tailBit_ne controlEncoding spec.ne)
          (controlValue, rawOneHotLabel occupied)
        by_cases hcontrol : control.get controlValue <;>
          simpa [controlledSwapGatesFor, EncodedBit.controlledSwapStep,
            hcontrol] using hread
      · have hread := EncodedBit.controlledSwapStep_get_observed_of_swap_ne
          (liftedControl control n)
          (tailBit controlEncoding spec.left)
          (tailBit controlEncoding spec.right)
          (tailBit controlEncoding observed)
          (liftedControl_ne_tailBit control spec.left)
          (liftedControl_ne_tailBit control spec.right)
          (tailBit_ne controlEncoding spec.ne)
          (tailBit_ne controlEncoding (Ne.symm hleft))
          (tailBit_ne controlEncoding (Ne.symm hright))
          (controlValue, rawOneHotLabel occupied)
        by_cases hcontrol : control.get controlValue <;>
          simpa [controlledSwapGatesFor, EncodedBit.controlledSwapStep,
            hcontrol, hleft, hright] using hread

/-- Gate list for a controlled public wire permutation.  The factor list is
reversed because gate-list execution is left-to-right whereas `List.prod`
acts by right-to-left function composition. -/
def controlledPermutationGates {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    List (EncodedBit.GateSpec (controlledEncoding controlEncoding n)) :=
  (factorSpecs perm).reverse.flatMap (controlledSwapGatesFor control)

/-- The synthesized gate list contains exactly three Toffolis per permutation
transposition. -/
theorem controlledPermutationGates_length {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    (controlledPermutationGates control perm).length =
      3 * (factorSpecs perm).length := by
  simp [controlledPermutationGates, List.length_flatMap, Nat.mul_comm]

private def isToffoliGate {Data : Type} {encoding : BinaryLabelEncoding Data} :
    EncodedBit.GateSpec encoding → Prop
  | .toffoli _ _ _ _ _ _ => True
  | _ => False

private theorem controlledPermutationGates_isToffoli {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    ∀ gate, gate ∈ controlledPermutationGates control perm →
      isToffoliGate gate := by
  intro gate hgate
  simp only [controlledPermutationGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨spec, _hspec, hgate⟩
  cases gate with
  | x target =>
      simp [controlledSwapGatesFor, EncodedBit.controlledSwapGates] at hgate
  | cnot controlBit target hct =>
      simp [controlledSwapGatesFor, EncodedBit.controlledSwapGates] at hgate
  | toffoli controlA controlB target hab ha hb =>
      trivial

private theorem toffoliList_count {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isToffoliGate gate) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (EncodedBit.GateSpec.programList gates).eventCost = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isToffoliGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isToffoliGate] at hgate
      | cnot control target hct => simp [isToffoliGate] at hgate
      | toffoli controlA controlB target hab ha hb =>
          change
            ResourcePool.count (.gate (.builtin "toffoli"))
                (ResourcePool.singleton (.gate (.builtin "toffoli")) +
                  (EncodedBit.GateSpec.programList rest).eventCost) =
              (EncodedBit.GateSpec.toffoli controlA controlB target hab ha hb ::
                rest).length
          rw [ResourcePool.count_add, ResourcePool.count_singleton_self,
            ih hrest]
          change 1 + rest.length = rest.length + 1
          exact Nat.add_comm _ _

private theorem toffoliList_unitDepth {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isToffoliGate gate) :
    (EncodedBit.GateSpec.programList gates).evaluatedEventDepth (fun _ => 1) =
      gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isToffoliGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isToffoliGate] at hgate
      | cnot control target hct => simp [isToffoliGate] at hgate
      | toffoli controlA controlB target hab ha hb =>
          change
            1 +
                (EncodedBit.GateSpec.programList rest).evaluatedEventDepth
                  (fun _ => 1) =
              (EncodedBit.GateSpec.toffoli controlA controlB target hab ha hb ::
                rest).length
          simp [ih hrest, Nat.add_comm]

/-- A compiled encoded-bit gate list contains no abstract oracle resource. -/
private theorem programList_queryCount_zero {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (label : QuantumAlg.Resource.SubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label.quantum)
        (EncodedBit.GateSpec.programList gates).eventCost = 0 :=
  EncodedBit.GateSpec.programList_quantumSubroutine_count_zero gates label.quantum

/-- The reversed transposition gate list realizes the product permutation on
canonical one-hot labels. -/
theorem controlledPermutationGates_step_rawOneHot {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (specs : List (SwapSpec n)) (controlValue : Control)
    (occupied : Fin n) :
    EncodedBit.GateSpec.stepList
        (specs.reverse.flatMap (controlledSwapGatesFor control))
        (controlValue, rawOneHotLabel occupied) =
      (controlValue,
        rawOneHotLabel
          (if control.get controlValue then
            (specs.map SwapSpec.perm).prod occupied
          else occupied)) := by
  induction specs with
  | nil =>
      simp [EncodedBit.GateSpec.stepList]
  | cons spec rest ih =>
      rw [List.reverse_cons, List.flatMap_append,
        EncodedBit.GateSpec.stepList_append]
      simp only [List.flatMap_singleton]
      rw [ih]
      rw [controlledSwapGatesFor_step_rawOneHot]
      by_cases hcontrol : control.get controlValue <;>
        simp [hcontrol, Equiv.Perm.mul_apply]

/-- Actual X/CNOT/Toffoli program implementing the controlled permutation. -/
def controlledPermutationProgram {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    UnitaryCircuit (Qubits (controlledEncoding controlEncoding n).width) :=
  EncodedBit.GateSpec.programList (controlledPermutationGates control perm)

/-- Exact Toffoli coefficient in the synthesized controlled-permutation
circuit. -/
theorem controlledPermutationProgram_toffoli_count {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (controlledPermutationProgram control perm).eventCost =
      3 * (factorSpecs perm).length := by
  unfold controlledPermutationProgram
  rw [toffoliList_count _
    (controlledPermutationGates_isToffoli control perm)]
  exact controlledPermutationGates_length control perm

/-- Exact unit-weight strict event depth of the synthesized controlled
permutation circuit. -/
theorem controlledPermutationProgram_unitDepth {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) :
    (controlledPermutationProgram control perm).evaluatedEventDepth
        (fun _ => 1) =
      3 * (factorSpecs perm).length := by
  unfold controlledPermutationProgram
  rw [toffoliList_unitDepth _
    (controlledPermutationGates_isToffoli control perm)]
  exact controlledPermutationGates_length control perm

/-- The synthesized program contains no oracle leaf, so every oracle query
counter is zero. -/
theorem controlledPermutationProgram_queryCount_zero {Control : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) {n : Nat}
    (perm : Equiv.Perm (Fin n)) (label : QuantumAlg.Resource.SubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label.quantum)
      (controlledPermutationProgram control perm).eventCost = 0 := by
  exact programList_queryCount_zero
    (controlledPermutationGates control perm) label

/-- Semantic update implemented by a controlled one-hot permutation. -/
def controlledPermutationStep {Control α : Type}
    {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding) (perm : Equiv.Perm α) :
    Control × α → Control × α :=
  fun value =>
    (value.1, if control.get value.1 then perm value.2 else value.2)

/-- On canonical one-hot inputs, the synthesized controlled permutation moves
the occupied wire by the public permutation exactly when the control bit is
set. -/
theorem controlledPermutationProgram_realizes_oneHot {Control α : Type}
    [Fintype α] {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding)
    (perm : Equiv.Perm α) :
    UnitaryCircuit.Realizes (controlledOneHotEncoding controlEncoding)
      (controlledPermutationProgram control (wirePermutation perm))
      (controlledPermutationStep control perm) where
  apply_encoded_ket := by
    rintro ⟨controlValue, x⟩
    have hstep :
        EncodedBit.GateSpec.stepList
            (controlledPermutationGates control (wirePermutation perm))
            (controlValue, oneHotLabel x) =
          (controlValue,
            oneHotLabel (if control.get controlValue then perm x else x)) := by
      unfold oneHotLabel controlledPermutationGates
      rw [controlledPermutationGates_step_rawOneHot]
      rw [factorSpecs_perm_prod]
      by_cases hcontrol : control.get controlValue
      · simp [hcontrol]
      · simp [hcontrol]
    change
      (EncodedBit.GateSpec.programList
          (controlledPermutationGates control (wirePermutation perm))).applyNormalized
          (NormalizedVector.ket
            ((controlledEncoding controlEncoding (Fintype.card α)).encode
              (controlValue, oneHotLabel x))) =
        NormalizedVector.ket
          ((controlledEncoding controlEncoding (Fintype.card α)).encode
            (controlValue,
              oneHotLabel
                (if control.get controlValue then perm x else x)))
    rw [(EncodedBit.GateSpec.realizesList
      (controlledPermutationGates control (wirePermutation perm))).apply_encoded_ket]
    rw [hstep]

/-- Pointwise canonical-input form of
`controlledPermutationProgram_realizes_oneHot`. -/
theorem controlledPermutationProgram_applyNormalized_oneHot {Control α : Type}
    [Fintype α] {controlEncoding : BinaryLabelEncoding Control}
    (control : EncodedBit controlEncoding)
    (perm : Equiv.Perm α) (controlValue : Control) (x : α) :
    (controlledPermutationProgram control (wirePermutation perm)).applyNormalized
        (NormalizedVector.ket
          ((controlledOneHotEncoding controlEncoding).encode (controlValue, x))) =
      NormalizedVector.ket
        ((controlledOneHotEncoding controlEncoding).encode
          (controlledPermutationStep control perm (controlValue, x))) :=
  (controlledPermutationProgram_realizes_oneHot control perm).apply_encoded_ket
    (controlValue, x)

end

end OneHotPermutation
end QuantumAlg

end
