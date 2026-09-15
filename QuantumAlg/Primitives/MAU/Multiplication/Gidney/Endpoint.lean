/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Layout
public import QuantumAlg.Primitives.MAU.Multiplication.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Requirement
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Resources

/-!
# Native unit multiplication with internally prepared auxiliary storage

The input supplies one word. The actual program prepares its missing zero
word and executes the proved native multiplier. Its complete output retains
both words and satisfies the independent reference-aware state target.
Every borrowed-restoration obligation is proved from the same execution.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Execution.OwnedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def canonicalInput (width : Nat) (modulus : Fin (2 ^ width + 1))
    (input : ExecutionState (Execution.Store (context width)) (context width).register) : Prop :=
  ∀ row column, (modulus.val ≤ (basisEquiv width row).val ∨
    modulus.val ≤ (basisEquiv width column).val) → input.quantumMarginal.matrix row column = 0

/-- Independent unit multiplication with an internally allocated zero auxiliary word.

**Input.**

- One supplied owned width-qubit word supported on canonical residues
x<N, in any normalized mixed state and with any external reference. The positive
fitted modulus N and unit coefficient in ZMod N are compilation parameters.
No additional initialized word is supplied by the caller; even N and N=1 are included.

**Output.**

- The complete output retains the supplied word and the internally
prepared auxiliary word. On canonical basis inputs it is (coefficient*x mod N,0).
The full joint-state target tensors the incoming state with the fixed zero
auxiliary basis and applies the independently specified exact multiplication
operator, preserving all reference correlations and relative phases.

**Resource budget.**

- One declared zero-word preparation event, twice the independent
MAC native pool, and 3*width native CNOT events for the literal word swap. Each MAC
pool caps its six controlled primitive coordinates by width*B(width), where B is
9 for widths at most two and 6*F(width+1)+12*F(width)+6*width+6 otherwise, with
F(w)=w*(39*clog(2,w)+1). Resident and owned auxiliary peaks are the same 2*width
dimension-two systems. Unit-duration depth is at most 1+2*width*B(width)+3*width.

**Success.**

- The unit result has probability one. The complete reference-aware
state promise holds for every admitted input. The empty-word case retains the
actual empty preparation event in its budget and allocates zero physical systems.

**Source.**

- Unit-inverse multiplication arithmetic [G17, paper.tex:186-211], using
the clean-auxiliary compute/uncompute specialization, and actual pivot-flip offsets
[G17, paper.tex:266-293,319-334] with internally borrowed HRS arithmetic
[HRS16, paper.tex:219-226,232-260].
-/
public def problem (width : Nat) (modulus : Fin (2 ^ width + 1)) (_positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) :
    Problem .quantum (context width) (preparedContext width) .unit where
  valid := canonicalInput width modulus
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [preparedRequirement width modulus coefficient]
  resources :=
    { events := preparedNativeBudget width
      resident := space (2 * width)
      auxiliary := space (2 * width) }
  depth := .quantum (fun _ => 1) (1 + eventBound width)

/-- Prepare the auxiliary word, run the actual native multiplier, and retain every live entry. -/
public def algorithm (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    Algorithm .quantum (context width) (preparedContext width) .unit where
  run :=
    { code := preparedCode width modulus coefficient
      output := Output.all (preparedContext width) .unit }

/-- Both the supplied word and internally prepared word remain in the public output. -/
public theorem gidneyUnitMultiplication_output_listing (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (algorithm width modulus coefficient).run.output.listing = (preparedContext width).keys := (rfl)

/-- The public problem includes its complete joint-state requirement. -/
public theorem gidneyUnitMultiplication_stateRequirement_count (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) :
    (problem width modulus positive coefficient).states.length = 1 := (rfl)

/-- The independent resident budget includes the source and its internally prepared auxiliary. -/
public theorem gidneyUnitMultiplication_resident_budget (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) :
    (problem width modulus positive coefficient).resources.resident = space (2 * width) := (rfl)

private theorem actual_borrowed (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) {Reference : Register} {H : Type} [Fintype H]
    (state : Execution.State (context width) Reference H) :
    (preparedCode width modulus coefficient).BorrowedRestored Reference state
      ((preparedCode width modulus coefficient).execute Reference state) := by
  let : Subsingleton (context width).borrowedClassicalShape.Value := by
    change Subsingleton (CShape.Value .unit)
    exact ⟨fun left right => by cases left; cases right; rfl⟩
  let preparation := Circuit.prepare (context width) auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width) (auxiliaryPreparation width)
  exact Circuit.borrowedRestored_seq preparation
    (Circuit.unitary (preparedUnitary width modulus coefficient)
      (gidneyPreparedUnitary_physical width modulus coefficient)) state
    (Circuit.borrowedRestored_prepare_noBorrowedQuantum rfl state auxiliaryKey
      (auxiliaryLayout width) (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
      (auxiliaryPreparation width))
    (Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (preparedUnitary width modulus coefficient)
      (gidneyPreparedUnitary_physical width modulus coefficient)
      (preparation.execute Reference state))

/-- The complete native execution satisfies the original unit domain and independent budgets. -/
public theorem main (width : Nat) (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) :
    ∃ candidate, Algorithm.Solves candidate (problem width modulus positive coefficient) := by
  refine ⟨algorithm width modulus coefficient, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = preparedRequirement width modulus coefficient :=
      List.mem_singleton.mp present
    subst requirement
    exact gidneyPreparedRequirement_holds width modulus coefficient
      (Output.all (preparedContext width) .unit) input
  · intro Reference input _valid
    exact actual_borrowed width modulus coefficient
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact gidneyPreparedCode_native_bound width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact gidneyPreparedCode_resident_bound width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact gidneyPreparedCode_auxiliary_bound width modulus coefficient path
  · intro _Reference _input _valid path _supported
    exact gidneyPreparedCode_depth_bound width modulus coefficient path

end

end QuantumAlg.MAU.Multiplication.Gidney
