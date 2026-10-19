/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# Exact coherent clean-carrier action of the two actual exponent programs

The embedding is a mathematical encoding
of the internally prepared unit/zero-auxiliary carrier. It is not a physical
conversion, a resource-free packing instruction, or an input certificate for
the final problem. The actual first and second programs share the same two
arithmetic words throughout. Their exact ket equations extend to arbitrary
coherent vectors and arbitrary mixed states entangled with a reference.
Only this clean carrier is compared; no dirty full-register commutation is
asserted. No measured recycling instrument is claimed by this module alone.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanSubspace

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Derive the intertwiner from exact actual ket action, rather than accept an
unrelated operator/instrument certificate at an executable endpoint. -/
private lemma intertwines_of_kets {R S : Register}
    (embedding : S.Index ↪ R.Index) (permutation : Equiv.Perm S.Index)
    (target : UnitaryOperator R)
    (actual : ∀ label, target.apply (NormalizedVector.ket (embedding label)) =
      NormalizedVector.ket (embedding (permutation label))) :
    (target : HilbertOperator R) * BasisEmbedding.matrix embedding =
      BasisEmbedding.matrix embedding *
        (UnitaryOperator.ofPerm permutation.symm : HilbertOperator S) := by
  classical
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  have actualColumn : target row (embedding column) =
      if row = embedding (permutation column) then 1 else 0 := by
    have equation := congrArg (fun vector : NormalizedVector R => vector row) (actual column)
    change HilbertOperator.applyVec (target : HilbertOperator R)
      (NormalizedVector.ket (embedding column) : HilbertVector R) row = _ at equation
    rw [HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] at equation
    exact equation
  have isolated :
      (∑ index : S.Index, if embedding index = row then
        (UnitaryOperator.ofPerm permutation.symm) index column else 0) =
        if embedding (permutation column) = row then 1 else 0 := by
    calc
      _ = (if embedding (permutation column) = row then
          (UnitaryOperator.ofPerm permutation.symm) (permutation column) column else 0) := by
        apply Finset.sum_eq_single (permutation column)
        · intro other _ different
          have inverseDifferent : permutation.symm other ≠ column := by
            intro same
            apply different
            calc
              other = permutation (permutation.symm other) :=
                (permutation.apply_symm_apply other).symm
              _ = permutation column := congrArg permutation same
          simp only [UnitaryOperator.ofPerm_entry, if_neg inverseDifferent, ite_self]
        · intro absent
          exact False.elim (absent (Finset.mem_univ _))
      _ = _ := by
        simp only [UnitaryOperator.ofPerm_entry, Equiv.symm_apply_apply, if_true]
  rw [actualColumn]
  exact (if_congr eq_comm rfl rfl).trans isolated.symm

/-- Both exponent values and the canonical unit seed may have arbitrary joint coherence. -/
def carrier (m ell N : Nat) [NeZero N] : Register where
  Index := (Fin (2 ^ (ell + m)) × Fin (2 ^ ell)) × (ZMod N)ˣ
  fintype := inferInstance
  decEq := inferInstance

/-- Actual physical register containing both old exponent words and the shared workspace. -/
def physical (m ell width : Nat) : Register :=
  (QubitLayout.canonical (totalQubits (registerParameters m ell width))).toQuantum.register

/-- Preserve both exponent labels and embed the unit into the actual power/zero-auxiliary words. -/
def embedding (m ell width N : Nat) [NeZero N]
    (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    (carrier m ell N).Index ↪ (physical m ell width).Index where
  toFun value :=
    (QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
      (cleanLabel m ell width N value.1.1 value.1.2 value.2)
  inj' := by
    intro left right same
    have labels :=
      (QubitLayout.canonical
        (totalQubits (registerParameters m ell width))).basisEquiv.symm.injective same
    have words := (groupEncoding m ell width).encode_injective labels
    have exponents := congrArg (fun value : GroupRegisters m ell width => value.1) words
    have workspace := congrArg (fun value : GroupRegisters m ell width => value.2) words
    apply Prod.ext
    · exact exponents
    · apply cleanUnitLabel_injective width N nontrivial fits
      exact congrArg (workspaceEncoding width).encode workspace

/-- Source arithmetic is translation by the selected two-exponent group element. -/
def action (m ell N : Nat) [NeZero N] (g x : (ZMod N)ˣ) :
    Equiv.Perm (carrier m ell N).Index :=
  Equiv.prodCongrRight fun exponents =>
    Equiv.mulLeft (oracleValue g x exponents.1.val exponents.2.val)

/-- The complete physical circuit supplies its own exact intertwiner on the clean carrier. -/
lemma group_intertwines (m ell width N : Nat) [NeZero N] (g x : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    HMul.hMul
      (α := Matrix (physical m ell width).Index (physical m ell width).Index ℂ)
      (β := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (γ := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      ((compiledGroupActionProgram m ell width N g x).matrix environment).val
      (BasisEmbedding.matrix (embedding m ell width N nontrivial fits)) =
    HMul.hMul
      (α := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (β := Matrix (carrier m ell N).Index (carrier m ell N).Index ℂ)
      (γ := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (BasisEmbedding.matrix (embedding m ell width N nontrivial fits))
      (UnitaryOperator.ofPerm (action m ell N g x).symm).val := by
  refine intertwines_of_kets (R := physical m ell width) (S := carrier m ell N)
    (embedding m ell width N nontrivial fits) (action m ell N g x)
    ((compiledGroupActionProgram m ell width N g x).matrix environment) ?_
  intro label
  exact compiledGroupActionProgram_applyLabel_clean m ell width N g x
    label.1.1 label.1.2 label.2 nontrivial fits

/-- Exact phase is retained for any coherent clean vector entangled with an untouched reference. -/
lemma group_coherent_reference (m ell width N : Nat) [NeZero N] (g x : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) (Reference : Register)
    (state : HilbertVector (Register.prod (carrier m ell N) Reference)) :
    (UnitaryOperator.prodTensor ((compiledGroupActionProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
      (Effect.extensionVector
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) =
    Effect.extensionVector
      (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
      ((UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (action m ell N g x).symm)
        (1 : UnitaryOperator Reference)).applyVec state) :=
  BasisEmbedding.applyVec_extension _ _ _
    (BasisEmbedding.reference_intertwines _ _ _
      (group_intertwines m ell width N g x nontrivial fits) Reference) state

/-- Every mixed/reference matrix entry survives the shared accumulator across both exponents. -/
lemma group_mixed_reference (m ell width N : Nat) [NeZero N] (g x : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) (Reference : Register)
    (state : DensityOperator (Register.prod (carrier m ell N) Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        ((compiledGroupActionProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference))
      (BasisEmbedding.density
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) =
    BasisEmbedding.density
      (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (action m ell N g x).symm)
          (1 : UnitaryOperator Reference)) state) :=
  BasisEmbedding.density_applyUnitary_reference _ _ _
    (group_intertwines m ell width N g x nontrivial fits) Reference state

/-- Exact first-program action on any canonical unit seed, before the second exponent runs. -/
private lemma first_clean (m ell width N : Nat) (g : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (seed : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    (firstExponentiationProgram m ell width N g).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical
          (totalQubits (registerParameters m ell width))).basisEquiv.symm
          (cleanLabel m ell width N a b seed))) =
    NormalizedVector.ket
      ((QubitLayout.canonical
        (totalQubits (registerParameters m ell width))).basisEquiv.symm
        (cleanLabel m ell width N a b (g ^ a.val * seed))) := by
  have actual := (firstExponentiationProgram_realizes (environment := environment) m ell
    width N g).apply_encoded_ket
    ((a, b), cleanWorkspace width N seed)
  have step : firstExponentiationStep m ell width N g
      ((a, b), cleanWorkspace width N seed) =
      ((a, b), cleanWorkspace width N (g ^ a.val * seed)) := by
    simp only [firstExponentiationStep]
    rw [exponentiationRawStep_cleanEndpoint
      (firstBits (registerParameters m ell width)) width N g seed a nontrivial fits]
  rw [step] at actual
  exact actual

/-- Exact second-program action uses the same words, with no intervening reinitialization. -/
private lemma second_clean (m ell width N : Nat) (x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (seed : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    (secondExponentiationProgram m ell width N x).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical
          (totalQubits (registerParameters m ell width))).basisEquiv.symm
          (cleanLabel m ell width N a b seed))) =
    NormalizedVector.ket
      ((QubitLayout.canonical
        (totalQubits (registerParameters m ell width))).basisEquiv.symm
        (cleanLabel m ell width N a b ((x⁻¹) ^ b.val * seed))) := by
  have actual := (secondExponentiationProgram_realizes (environment := environment) m ell
    width N x).apply_encoded_ket
    ((a, b), cleanWorkspace width N seed)
  have step : secondExponentiationStep m ell width N x
      ((a, b), cleanWorkspace width N seed) =
      ((a, b), cleanWorkspace width N ((x⁻¹) ^ b.val * seed)) := by
    simp only [secondExponentiationStep]
    rw [exponentiationRawStep_cleanEndpoint ell width N x⁻¹ seed b nontrivial fits]
  rw [step] at actual
  exact actual

/-- Reversed stream order is compared only on the proved clean carrier. -/
def reversedProgram (m ell width N : Nat) (g x : (ZMod N)ˣ) :=
  (secondExponentiationProgram m ell width N x).seq
    (firstExponentiationProgram m ell width N g)

private lemma reversed_intertwines (m ell width N : Nat) [NeZero N] (g x : (ZMod N)ˣ)
    (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    HMul.hMul
      (α := Matrix (physical m ell width).Index (physical m ell width).Index ℂ)
      (β := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (γ := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      ((reversedProgram m ell width N g x).matrix environment).val
      (BasisEmbedding.matrix (embedding m ell width N nontrivial fits)) =
    HMul.hMul
      (α := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (β := Matrix (carrier m ell N).Index (carrier m ell N).Index ℂ)
      (γ := Matrix (physical m ell width).Index (carrier m ell N).Index ℂ)
      (BasisEmbedding.matrix (embedding m ell width N nontrivial fits))
      (UnitaryOperator.ofPerm (action m ell N g x).symm).val := by
  refine intertwines_of_kets (R := physical m ell width) (S := carrier m ell N)
    (embedding m ell width N nontrivial fits) (action m ell N g x)
    ((reversedProgram m ell width N g x).matrix environment) ?_
  intro label
  change (reversedProgram m ell width N g x).applyNormalized environment _ = _
  have sequential := UnitaryCircuit.applyNormalized_seq (environment := environment)
    (secondExponentiationProgram m ell width N x)
    (firstExponentiationProgram m ell width N g)
    (NormalizedVector.ket
      ((QubitLayout.canonical
        (totalQubits (registerParameters m ell width))).basisEquiv.symm
        (cleanLabel m ell width N label.1.1 label.1.2 label.2)))
  have second := second_clean (environment := environment) m ell width N x
    label.1.1 label.1.2 label.2 nontrivial fits
  have first := first_clean (environment := environment) m ell width N g label.1.1 label.1.2
    ((x⁻¹) ^ label.1.2.val * label.2) nontrivial fits
  refine (sequential.trans ((congrArg
    ((firstExponentiationProgram m ell width N g).applyNormalized environment) second).trans
      first)).trans ?_
  change NormalizedVector.ket _ = NormalizedVector.ket _
  apply congrArg (fun seed : (ZMod N)ˣ => NormalizedVector.ket
    ((QubitLayout.canonical
      (totalQubits (registerParameters m ell width))).basisEquiv.symm
      (cleanLabel m ell width N label.1.1 label.1.2 seed)))
  change g ^ label.1.1.val * ((x⁻¹) ^ label.1.2.val * label.2) =
    oracleValue g x label.1.1.val label.1.2.val * label.2
  simp only [oracleValue, inv_pow]
  ac_rfl

/-- Swapping the two actual exponent streams preserves phase on the clean carrier,
including arbitrary coherence with an untouched reference. -/
lemma streams_commute_coherent_reference (m ell width N : Nat) [NeZero N]
    (g x : (ZMod N)ˣ) (nontrivial : 1 < N) (fits : N < 2 ^ width)
    (Reference : Register)
    (state : HilbertVector (Register.prod (carrier m ell N) Reference)) :
    (UnitaryOperator.prodTensor ((compiledGroupActionProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
      (Effect.extensionVector
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) =
    (UnitaryOperator.prodTensor ((reversedProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
      (Effect.extensionVector
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) := by
  exact (group_coherent_reference m ell width N g x nontrivial fits Reference state).trans
    (BasisEmbedding.applyVec_extension _ _ _
      (BasisEmbedding.reference_intertwines _ _ _
        (reversed_intertwines m ell width N g x nontrivial fits) Reference) state).symm

/-- Swapping the two actual exponent streams preserves every clean mixed/reference block.
This is not a claim that their total dirty-register unitary operators commute. -/
lemma streams_commute_mixed_reference (m ell width N : Nat) [NeZero N]
    (g x : (ZMod N)ˣ) (nontrivial : 1 < N) (fits : N < 2 ^ width)
    (Reference : Register)
    (state : DensityOperator (Register.prod (carrier m ell N) Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        ((compiledGroupActionProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference))
      (BasisEmbedding.density
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) =
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor ((reversedProgram m ell width N g x).matrix environment)
        (1 : UnitaryOperator Reference))
      (BasisEmbedding.density
        (BasisEmbedding.withReference (embedding m ell width N nontrivial fits) Reference)
        state) := by
  exact (group_mixed_reference m ell width N g x nontrivial fits Reference state).trans
    (BasisEmbedding.density_applyUnitary_reference _ _ _
      (reversed_intertwines m ell width N g x nontrivial fits) Reference state).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanSubspace
