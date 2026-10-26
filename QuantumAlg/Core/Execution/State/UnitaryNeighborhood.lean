/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Observe
public import QuantumAlg.Core.Execution.Reindex
public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Gate.OperatorNorm
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.State.Density
import all Mathlib.Data.Complex.Basic

/-!
# State targets in an operator-norm neighborhood

A target specifies a mathematical unitary, a normalized joint input and an
observation of actual systems with their external reference. Its neighborhood
contains the outputs of system unitaries at the stated full-phase operator-norm
distance. The reference is acted on by the identity, including its correlations
with the system. No circuit, execution history or resource metadata occurs in
this target. The actual density block retains its own probability weight.
-/

namespace QuantumAlg

/-- A closed mathematical family of approximately transformed joint states. -/
public structure UnitaryNeighborhood (R : Register) where
  /-- Number of physical systems in the independently specified input. -/
  width : Nat
  /-- The supplied physical layout. -/
  layout : QuantumLayout width
  /-- Actual output systems whose state is observed. -/
  selection : Finset (Fin width)
  /-- Arbitrary external reference retained by the observation. -/
  reference : Register
  /-- Exact coordinate identification of the observed systems and reference. -/
  basis : (Register.prod (layout.selectedRegister selection) reference).Index ≃ R.Index
  /-- Independently supplied input, including system-reference correlations. -/
  input : DensityOperator (Register.prod layout.register reference)
  /-- The input represents a normalized state. -/
  normalized : input.IsNormalized
  /-- Mathematical target action on the system alone. -/
  operator : UnitaryOperator layout.register
  /-- Allowed full-phase system operator-norm error. -/
  error : ℝ
  /-- Nonnegative errors admit the target itself, even for impossible output blocks. -/
  nonnegative : 0 ≤ error

namespace UnitaryNeighborhood

noncomputable section

variable {R S : Register}

/-- Observe an actual mathematical system action, leaving the reference untouched. -/
public def state (target : UnitaryNeighborhood R)
    (actual : UnitaryOperator target.layout.register) : DensityOperator R :=
  (DensityOperator.observeSelectionWithReference target.layout target.selection target.reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor actual (1 : UnitaryOperator target.reference))
      target.input)).reindex target.basis

/-- The complete observed block is the mass-weighted output of a nearby system unitary. -/
public def Holds (target : UnitaryNeighborhood R) (actualState : DensityOperator R) : Prop :=
  ∃ actual : UnitaryOperator target.layout.register,
    HilbertOperator.opNorm ((actual : HilbertOperator target.layout.register) -
      (target.operator : HilbertOperator target.layout.register)) ≤ target.error ∧
    actualState.matrix = (actualState.mass : ℝ) • (target.state actual).matrix

/-- Basis transport changes no system action, error, input or selected physical system. -/
@[expose, implicit_reducible]
public def reindex (target : UnitaryNeighborhood R) (basis : R.Index ≃ S.Index) :
    UnitaryNeighborhood S :=
  { target with basis := target.basis.trans basis }

/-- Every observed candidate state remains normalized. -/
public lemma state_normalized (target : UnitaryNeighborhood R)
    (actual : UnitaryOperator target.layout.register) :
    (target.state actual).IsNormalized := by
  change (target.state actual).mass = 1
  rw [state, DensityOperator.reindex_mass, DensityOperator.observeSelectionWithReference_mass,
    DensityOperator.applyUnitary_mass]
  exact target.normalized

/-- Impossible blocks require no conditional-state normalization. -/
public lemma holds_zero (target : UnitaryNeighborhood R) :
    target.Holds (DensityOperator.zero R) := by
  refine ⟨target.operator, ?_, ?_⟩
  · simpa only [sub_self, HilbertOperator.opNorm_zero] using target.nonnegative
  · simp

/-- Transporting a target transports each candidate density operator exactly. -/
public lemma reindex_state (target : UnitaryNeighborhood R)
    (basis : R.Index ≃ S.Index) (actual : UnitaryOperator target.layout.register) :
    (target.reindex basis).state actual = (target.state actual).reindex basis := by
  exact (DensityOperator.reindex_trans _ target.basis basis).symm

/-- Exact coordinate transport preserves the neighborhood and its probability weight. -/
public lemma reindex_holds_iff (target : UnitaryNeighborhood R)
    (basis : R.Index ≃ S.Index) (actualState : DensityOperator R) :
    (target.reindex basis).Holds (actualState.reindex basis) ↔ target.Holds actualState := by
  constructor
  · rintro ⟨actual, close, same⟩
    refine ⟨actual, close, ?_⟩
    rw [reindex_state, DensityOperator.reindex_mass] at same
    ext row column
    simpa only [DensityOperator.reindex_entry,
      Equiv.symm_apply_apply, Matrix.smul_apply] using
      congrArg (fun matrix => matrix (basis row) (basis column)) same
  · rintro ⟨actual, close, same⟩
    refine ⟨actual, close, ?_⟩
    rw [reindex_state, DensityOperator.reindex_mass]
    ext row column
    simpa only [DensityOperator.reindex_entry, Matrix.smul_apply] using
      congrArg (fun matrix => matrix (basis.symm row) (basis.symm column)) same

end
end UnitaryNeighborhood
end QuantumAlg
