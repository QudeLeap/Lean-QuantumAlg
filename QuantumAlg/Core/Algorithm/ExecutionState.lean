/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Measure.Instrument

/-!
# Internal state of finite classical and quantum execution

A classical value labels a subnormalized density operator. The sum of the
block traces is the total mass, so impossible classical values have zero
blocks. Z measurement records its outcome together with the quantum conditional
state; a subsequent unitary is selected from the actual classical value.

The block representation combines mixed states [dW19, qcnotes.tex:5381] with
the probability-bearing measurement updates [dW19, qcnotes.tex:5409]. The
maps here are mathematical state transformations; storage and execution costs
are supplied by the typed execution language, never by these state carriers.
-/

section

open scoped ComplexOrder

namespace QuantumAlg

/-- A finite classical register correlated with one full quantum register.
Each block includes its probability weight; the complete state has mass at
most one. No product-state assumption separates the quantum subsystems. -/
public structure ExecutionState (Classical : Type) [Fintype Classical] (R : Register) where
  /-- Quantum conditional operator weighted by the classical probability. -/
  block : Classical → DensityOperator R
  /-- The sum of the classical probabilities is at most one. -/
  total_le_one : ∑ value, (block value).mass ≤ 1

namespace ExecutionState

noncomputable section

variable {C D Outcome : Type} [Fintype C] [Fintype D] [Fintype Outcome]
  {R : Register}

/-- Total probability mass of the joint state. -/
public def mass (state : ExecutionState C R) : ℝ := ∑ value, (state.block value).mass

/-- Normalization concerns the joint state, not each conditional block. -/
public def IsNormalized (state : ExecutionState C R) : Prop := state.mass = 1

lemma mass_nonneg (state : ExecutionState C R) : 0 ≤ state.mass :=
  Finset.sum_nonneg (fun value _ => (state.block value).mass_nonneg)

lemma mass_le_one (state : ExecutionState C R) : state.mass ≤ 1 :=
  state.total_le_one

@[ext]
lemma ext {left right : ExecutionState C R}
    (h : ∀ value, left.block value = right.block value) : left = right := by
  cases left
  cases right
  congr
  exact funext h

/-- The impossible complete state has a zero quantum block at every value. -/
public def zero : ExecutionState C R where
  block _ := DensityOperator.zero R
  total_le_one := by simp

@[simp] lemma zero_block (value : C) :
    (zero : ExecutionState C R).block value = DensityOperator.zero R := rfl

@[simp] lemma zero_mass : (zero : ExecutionState C R).mass = 0 := by
  simp [mass]

/-- One classical block has at most the total state's mass. -/
lemma block_mass_le (state : ExecutionState C R) (value : C) :
    (state.block value).mass ≤ state.mass :=
  Finset.single_le_sum (fun other _ => (state.block other).mass_nonneg)
    (Finset.mem_univ value)

/-- A classical value of probability zero carries the zero quantum operator. -/
lemma block_eq_zero_of_mass_eq_zero (state : ExecutionState C R) (value : C)
    (h : (state.block value).mass = 0) :
    state.block value = DensityOperator.zero R :=
  (state.block value).eq_zero_of_mass_eq_zero h

/-- Insert a definite classical value beside an arbitrary quantum state. -/
public def ofValue [DecidableEq C] (value : C) (ρ : DensityOperator R) :
    ExecutionState C R where
  block other := if other = value then ρ else DensityOperator.zero R
  total_le_one := by simpa only [apply_ite DensityOperator.mass, DensityOperator.zero_mass,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using ρ.mass_le_one

@[simp] lemma ofValue_block [DecidableEq C] (value other : C) (ρ : DensityOperator R) :
    (ofValue value ρ).block other = if other = value then ρ else DensityOperator.zero R := rfl

@[simp] lemma ofValue_mass [DecidableEq C] (value : C) (ρ : DensityOperator R) :
    (ofValue value ρ).mass = ρ.mass := by simp [mass, apply_ite]

/-- Computational-basis measurement retains the old classical value and
records the observed result with its probability-bearing quantum poststate. -/
def measureZ [DecidableEq Outcome] (state : ExecutionState C R)
    (readout : R.Index → Outcome) : ExecutionState (C × Outcome) R where
  block result := ZMeasurement.branch readout result.2 (state.block result.1)
  total_le_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [ZMeasurement.sum_branch_mass]
    exact state.total_le_one

@[simp] lemma measureZ_block [DecidableEq Outcome] (state : ExecutionState C R)
    (readout : R.Index → Outcome) (value : C) (outcome : Outcome) :
    (state.measureZ readout).block (value, outcome) =
      ZMeasurement.branch readout outcome (state.block value) := rfl

/-- Recording a Z result preserves the complete state's total mass. -/
lemma measureZ_mass [DecidableEq Outcome] (state : ExecutionState C R)
    (readout : R.Index → Outcome) : (state.measureZ readout).mass = state.mass := by
  simp only [mass, Fintype.sum_prod_type, measureZ_block, ZMeasurement.sum_branch_mass]

/-- The later result distribution retains each earlier classical probability. -/
lemma measureZ_first_mass [DecidableEq Outcome] (state : ExecutionState C R)
    (readout : R.Index → Outcome) (value : C) :
    ∑ outcome, ((state.measureZ readout).block (value, outcome)).mass =
      (state.block value).mass := by
  simp only [measureZ_block]
  exact ZMeasurement.sum_branch_mass readout (state.block value)

/-- A unitary step reads the actual classical value to select its operator.
The instruction interpreter supplies this family from its typed conditional
gate syntax, not from a separate channel or cost witness. -/
public def applyUnitary (state : ExecutionState C R) (operator : C → UnitaryOperator R) :
    ExecutionState C R where
  block value := DensityOperator.applyUnitary (operator value) (state.block value)
  total_le_one := by
    simp_rw [DensityOperator.applyUnitary_mass]
    exact state.total_le_one

@[simp] lemma applyUnitary_block (state : ExecutionState C R)
    (operator : C → UnitaryOperator R) (value : C) :
    (state.applyUnitary operator).block value =
      DensityOperator.applyUnitary (operator value) (state.block value) := rfl

/-- A selected unitary does not change the probability of its classical branch. -/
lemma applyUnitary_block_mass (state : ExecutionState C R)
    (operator : C → UnitaryOperator R) (value : C) :
    ((state.applyUnitary operator).block value).mass = (state.block value).mass := by
  simp only [applyUnitary_block, DensityOperator.applyUnitary_mass]

/-- Conditional unitary execution preserves the total mass. -/
lemma applyUnitary_mass (state : ExecutionState C R) (operator : C → UnitaryOperator R) :
    (state.applyUnitary operator).mass = state.mass := by
  simp only [mass, applyUnitary_block_mass]

/-- Quantum marginal obtained by summing the classical blocks. This
mathematical projection is not an instruction that frees classical storage. -/
public def quantumMarginal (state : ExecutionState C R) : DensityOperator R where
  matrix := ∑ value, (state.block value).matrix
  positive := Matrix.posSemidef_sum _ (fun value _ => (state.block value).positive)
  trace_le_one := by
    rw [Matrix.trace_sum, Complex.re_sum]
    exact state.total_le_one

lemma quantumMarginal_mass (state : ExecutionState C R) :
    state.quantumMarginal.mass = state.mass := by
  simp only [DensityOperator.mass, quantumMarginal, Matrix.trace_sum, Complex.re_sum, mass]

@[simp] lemma ofValue_quantumMarginal [DecidableEq C] (value : C)
    (ρ : DensityOperator R) : (ofValue value ρ).quantumMarginal = ρ := by
  apply DensityOperator.ext
  simp [quantumMarginal, ofValue, apply_ite]

omit [Fintype D] in
private lemma sum_fiber_trace [DecidableEq D] (state : ExecutionState C R)
    (f : C → D) (value : D) :
    (∑ input, if f input = value then (state.block input).matrix else 0).trace.re =
      ∑ input, if f input = value then (state.block input).mass else 0 := by
  rw [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro input _
  split <;> simp_all [DensityOperator.mass]

/-- Push the classical value through a finite deterministic function, summing
exactly the blocks with the same resulting value. Quantum coherence inside
each block is retained. -/
public def mapClassical [DecidableEq D] (state : ExecutionState C R) (f : C → D) :
    ExecutionState D R where
  block value :=
    { matrix := ∑ input, if f input = value then (state.block input).matrix else 0
      positive := Matrix.posSemidef_sum _ (fun input _ => by
        split
        · exact (state.block input).positive
        · exact Matrix.PosSemidef.zero)
      trace_le_one := by
        rw [sum_fiber_trace]
        apply le_trans _ state.total_le_one
        apply Finset.sum_le_sum
        intro input _
        split
        · exact le_rfl
        · exact (state.block input).mass_nonneg }
  total_le_one := by
    change (∑ value, (∑ input,
      if f input = value then (state.block input).matrix else 0).trace.re) ≤ 1
    simp_rw [sum_fiber_trace]
    rw [Finset.sum_comm]
    simpa using state.total_le_one

/-- Deterministic classical processing preserves total probability mass even
when several input values collide. -/
lemma mapClassical_mass [DecidableEq D] (state : ExecutionState C R) (f : C → D) :
    (state.mapClassical f).mass = state.mass := by
  change (∑ value, (∑ input,
    if f input = value then (state.block input).matrix else 0).trace.re) = state.mass
  simp_rw [sum_fiber_trace]
  rw [Finset.sum_comm]
  simp [mass]

/-- Classical processing changes no entry of the quantum marginal, including
coherences with any reference subsystem retained in the full register. -/
lemma mapClassical_quantumMarginal [DecidableEq D]
    (state : ExecutionState C R) (f : C → D) :
    (state.mapClassical f).quantumMarginal = state.quantumMarginal := by
  apply DensityOperator.ext
  change (∑ value, ∑ input,
    if f input = value then (state.block input).matrix else 0) =
      ∑ input, (state.block input).matrix
  rw [Finset.sum_comm]
  simp

@[simp] lemma mapClassical_id [DecidableEq C] (state : ExecutionState C R) :
    state.mapClassical id = state := by
  apply ext
  intro value
  apply DensityOperator.ext
  change (∑ input, if input = value then (state.block input).matrix else 0) =
    (state.block value).matrix
  simp

/-- Successive deterministic classical updates compose on the actual quantum blocks.
Every intermediate collision is summed, preserving complete quantum coherences. -/
public lemma executionState_mapClassical_comp {E : Type} [Fintype E]
    [DecidableEq D] [DecidableEq E] (state : ExecutionState C R)
    (first : C → D) (second : D → E) :
    (state.mapClassical first).mapClassical second =
      state.mapClassical (second ∘ first) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  change (∑ middle : D, if second middle = result then
    (∑ input : C, if first input = middle then (state.block input).matrix else 0) else 0) =
      ∑ input : C, if second (first input) = result then (state.block input).matrix else 0
  have distribute (middle : D) :
      (if second middle = result then
        (∑ input : C, if first input = middle then (state.block input).matrix else 0) else 0) =
      ∑ input : C, if first input = middle then
        (if second middle = result then (state.block input).matrix else 0) else 0 := by
    by_cases selected : second middle = result
    · simp only [selected, if_true]
    · simp only [selected, if_false, ite_self, Finset.sum_const_zero]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Reading a stored classical value after an update selects the same unitary
on every original block that contributes to that value. This is the internal
read-after-write bridge for measured classical control. -/
lemma applyUnitary_mapClassical [DecidableEq D] (state : ExecutionState C R)
    (update : C → D) (operator : D → UnitaryOperator R) :
    (state.mapClassical update).applyUnitary operator =
      (state.applyUnitary fun value => operator (update value)).mapClassical update := by
  apply ext
  intro value
  apply DensityOperator.ext
  change (operator value : HilbertOperator R) *
      (∑ input, if update input = value then (state.block input).matrix else 0) *
      (operator value : HilbertOperator R).conjTranspose =
    ∑ input, if update input = value then
      (operator (update input) : HilbertOperator R) * (state.block input).matrix *
        (operator (update input) : HilbertOperator R).conjTranspose else 0
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro input _
  by_cases same : update input = value
  · simp only [same, if_true]
  · simp only [same, if_false, Matrix.mul_zero, Matrix.zero_mul]

end

end ExecutionState
end QuantumAlg

end
