module

import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.SingleQubit.Last.Binary
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Core.Base.UnitaryCircuit.Space
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.WireAddress

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# General two-interval streaming invariant

The native streaming program implements the fixed two-column table. Its
two-interval invariant tracks the emitted word and remaining memory through
the ordered sequence of table applications.

`input = false` is the actual initial memory. A fresh emitted qubit starts at
zero before each table application. Word indices are big-endian: the next
emitted bit has weight `h`, and the remaining suffix has value below `h`.

For nonzero cut, memory false/true denotes the normalized disjoint intervals
[0,cut) and [cut,total). For cut zero, the full interval is paired with the
unchanged input memory. The second case is necessary: H tensor identity does
not reset an arbitrary memory-one input. Only the legal initial memory-zero
column is claimed to finish with memory zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Amplitude of one member of a normalized interval of the given cardinality. -/
def invSqrt (count : Nat) : ℝ := (Real.sqrt (count : ℝ))⁻¹

/-- The nonnegative branching coefficient, written to expose normalization cancellation. -/
def weight (total part : Nat) : ℝ := Real.sqrt (part : ℝ) * invSqrt total

/-- This coefficient is exactly the nonnegative root specified in the fixed table. -/
lemma weight_eq_sqrt_ratio (total part : Nat) :
    weight total part = Real.sqrt ((part : ℝ) / (total : ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  rfl

/-- Empty intervals have zero amplitude everywhere, including their endpoints. -/
def interval (lower upper x : Nat) : ℝ :=
  if lower ≤ x ∧ x < upper then invSqrt (upper - lower) else 0

/-- Every nonempty child interval has the same parent-normalized amplitude. -/
lemma weight_mul_invSqrt (total part : Nat) (positive : 0 < part) :
    weight total part * invSqrt part = invSqrt total := by
  have nonzero : Real.sqrt (part : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast positive)).ne'
  unfold weight invSqrt
  calc
    _ = (Real.sqrt (part : ℝ) * (Real.sqrt (part : ℝ))⁻¹) *
        (Real.sqrt (total : ℝ))⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ nonzero, one_mul]

/-- The normalization identity also handles empty children without dividing by their length. -/
lemma weight_mul_interval (total lower upper x : Nat) :
    weight total (upper - lower) * interval lower upper x =
      if lower ≤ x ∧ x < upper then invSqrt total else 0 := by
  by_cases member : lower ≤ x ∧ x < upper
  · rw [interval, if_pos member, if_pos member]
    exact weight_mul_invSqrt total (upper - lower) (by omega)
  · simp only [interval, if_neg member, mul_zero]

/-- The cut-zero coefficient is the usual positive Hadamard coefficient. -/
lemma weight_double (half : Nat) (positive : 0 < half) :
    weight (2 * half) half = (Real.sqrt 2)⁻¹ := by
  have positiveReal : (0 : ℝ) < half := by exact_mod_cast positive
  rw [weight_eq_sqrt_ratio]
  have ratio : (half : ℝ) / ((2 * half : Nat) : ℝ) = 1 / 2 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt positiveReal]
  rw [ratio, Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]

/-- The prescribed two-column map; rows are (emitted bit, next memory). -/
def table (half cut : Nat) (input emitted next : Bool) : ℝ :=
  if cut = 0 then
    if next = input then weight (2 * half) half else 0
  else if cut = half then
    if emitted = input ∧ next = false then 1 else 0
  else if cut < half then
    if input then
      if emitted then
        if next then weight (2 * half - cut) (half - cut)
        else weight (2 * half - cut) cut
      else if next then weight (2 * half - cut) (half - cut) else 0
    else if emitted = false ∧ next = false then 1 else 0
  else if input then
    if emitted = true ∧ next = true then 1 else 0
  else if emitted then
    if next then 0 else weight cut (cut - half)
  else if next then weight cut (2 * half - cut)
  else weight cut (cut - half)

/-- The complete suffix vector, including the final memory rather than only its marginal. -/
def model (total cut : Nat) (input : Bool) (x : Nat) (final : Bool) : ℝ :=
  if cut = 0 then
    if final = input then interval 0 total x else 0
  else if final then 0
  else if input then interval cut total x else interval 0 cut x

/-- Both nonzero-cut columns occupy disjoint suffix intervals and end in memory zero. -/
lemma model_nonzero_cut (total cut : Nat) (nonzero : cut ≠ 0) (x : Nat) :
    model total cut false x false = interval 0 cut x ∧
    model total cut true x false = interval cut total x ∧
    model total cut false x true = 0 ∧ model total cut true x true = 0 := by
  simp [model, nonzero]

/-- Zero cut preserves arbitrary memory; this deliberately does not assert a universal reset. -/
lemma model_zero_cut (total : Nat) (input : Bool) (x : Nat) (final : Bool) :
    model total 0 input x final =
      if final = input then interval 0 total x else 0 := rfl

private lemma step_zero (half : Nat) (positive : 0 < half)
    (input emitted final : Bool) (x : Nat) (bound : x < half) :
    model (2 * half) 0 input (if emitted then half + x else x) final =
      table half 0 input emitted false * model half 0 false x final +
      table half 0 input emitted true * model half 0 true x final := by
  have normalization := weight_mul_invSqrt (2 * half) half positive
  have lowBound : x < 2 * half := by omega
  have highBound : half + x < 2 * half := by omega
  cases input <;> cases emitted <;> cases final <;>
    simp [table, model, interval, bound, lowBound, highBound, normalization]

private lemma step_half (half : Nat) (positive : 0 < half)
    (input emitted final : Bool) (x : Nat) (bound : x < half) :
    model (2 * half) half input (if emitted then half + x else x) final =
      table half half input emitted false * model half 0 false x final +
      table half half input emitted true * model half 0 true x final := by
  have nonzero : half ≠ 0 := Nat.ne_of_gt positive
  have length : 2 * half - half = half := by omega
  have lower : ¬ half ≤ x := by omega
  have upper : half + x < 2 * half := by omega
  have outside : ¬ half + x < half := by omega
  cases input <;> cases emitted <;> cases final <;>
    simp [table, model, interval, nonzero, length, bound, lower, upper, outside]

private lemma step_low (half cut : Nat) (positive : 0 < cut) (low : cut < half)
    (input emitted final : Bool) (x : Nat) (bound : x < half) :
    model (2 * half) cut input (if emitted then half + x else x) final =
      table half cut input emitted false * model half cut false x final +
      table half cut input emitted true * model half cut true x final := by
  have nonzero : cut ≠ 0 := Nat.ne_of_gt positive
  have different : cut ≠ half := Nat.ne_of_lt low
  have lowerWeight := weight_mul_interval (2 * half - cut) 0 cut x
  have upperWeight := weight_mul_interval (2 * half - cut) cut half x
  simp only [Nat.sub_zero] at lowerWeight
  cases input <;> cases emitted <;> cases final <;>
    simp [table, model, nonzero, different, low, lowerWeight, upperWeight] <;>
    simp only [interval, Nat.sub_zero] <;>
    split_ifs <;> simp_all <;> omega

private lemma step_high (half cut : Nat) (high : half < cut) (cutBound : cut < 2 * half)
    (input emitted final : Bool) (x : Nat) (bound : x < half) :
    model (2 * half) cut input (if emitted then half + x else x) final =
      table half cut input emitted false * model half (cut - half) false x final +
      table half cut input emitted true * model half (cut - half) true x final := by
  have nonzero : cut ≠ 0 := by omega
  have remainderNonzero : cut - half ≠ 0 := by omega
  have different : cut ≠ half := by omega
  have notLow : ¬ cut < half := by omega
  have length : half - (cut - half) = 2 * half - cut := by omega
  have lowerWeight := weight_mul_interval cut 0 (cut - half) x
  have upperWeight := weight_mul_interval cut (cut - half) half x
  simp only [Nat.sub_zero] at lowerWeight
  rw [length] at upperWeight
  cases input <;> cases emitted <;> cases final <;>
    simp [table, model, nonzero, remainderNonzero, different, notLow,
      lowerWeight, upperWeight] <;>
    simp only [interval, Nat.sub_zero, length] <;>
    split_ifs <;> simp_all <;> omega

/-- The exact fixed table intertwines the two interval states at every width and both boundaries. -/
lemma model_step (half cut : Nat) (positive : 0 < half) (cutBound : cut < 2 * half)
    (input emitted final : Bool) (x : Nat) (bound : x < half) :
    model (2 * half) cut input (if emitted then half + x else x) final =
      table half cut input emitted false * model half (cut % half) false x final +
      table half cut input emitted true * model half (cut % half) true x final := by
  by_cases zero : cut = 0
  · subst cut
    simpa only [Nat.zero_mod] using step_zero half positive input emitted final x bound
  by_cases middle : cut = half
  · subst cut
    simpa only [Nat.mod_self] using step_half half positive input emitted final x bound
  by_cases low : cut < half
  · rw [Nat.mod_eq_of_lt low]
    exact step_low half cut (by omega) low input emitted final x bound
  · have high : half < cut := by omega
    have remainder : cut % half = cut - half := by
      rw [Nat.mod_eq_sub_mod high.le, Nat.mod_eq_of_lt (by omega)]
    rw [remainder]
    exact step_high half cut high cutBound input emitted final x bound

/-- Execute the fixed table from the most significant bit toward the least significant bit. -/
def generated (r : Nat) : Nat → Bool → Nat → Bool → ℝ
  | 0, input, x, final => if x = 0 ∧ final = input then 1 else 0
  | m + 1, input, x, final =>
      let half := 2 ^ m
      let cut := r % (2 * half)
      let emitted := decide (half ≤ x)
      table half cut input emitted false * generated r m false (x % half) final +
      table half cut input emitted true * generated r m true (x % half) final

/-- General vector-level induction, retaining the entire final memory coordinate. -/
lemma generated_eq_model (r m : Nat) (input : Bool) (x : Nat) (final : Bool)
    (bound : x < 2 ^ m) :
    generated r m input x final = model (2 ^ m) (r % 2 ^ m) input x final := by
  induction m generalizing input x final with
  | zero =>
      have value : x = 0 := by norm_num at bound; omega
      subst x
      simp [generated, model, interval, invSqrt, Nat.mod_one]
  | succ m ih =>
      let half := 2 ^ m
      have positive : 0 < half := by dsimp [half]; positivity
      have width : 2 ^ (m + 1) = 2 * half := by simp [half, pow_succ, Nat.mul_comm]
      have remainderBound : x % half < half := Nat.mod_lt x positive
      have residue : (r % (2 * half)) % half = r % half :=
        Nat.mod_mod_of_dvd r (Nat.dvd_mul_left half 2)
      have assembled : (if decide (half ≤ x) then half + x % half else x % half) = x := by
        by_cases present : half ≤ x
        · have remainder : x % half = x - half := by
            rw [Nat.mod_eq_sub_mod present, Nat.mod_eq_of_lt (by omega)]
          simp only [present, decide_true, ↓reduceIte, remainder]
          omega
        · simp only [present, decide_false, Bool.false_eq_true, ↓reduceIte,
            Nat.mod_eq_of_lt (by omega : x < half)]
      have lower := ih false (x % half) final remainderBound
      have upper := ih true (x % half) final remainderBound
      have recursive := model_step half (r % (2 * half)) positive
        (Nat.mod_lt r (by omega)) input (decide (half ≤ x)) final (x % half) remainderBound
      rw [residue, assembled] at recursive
      rw [generated, lower, upper, width]
      exact recursive.symm

/-- The actual legal initialization produces exactly [0,r), with a zero final memory qubit. -/
lemma initialized_amplitude (r m x : Nat) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (wordBound : x < 2 ^ m) (final : Bool) :
    generated r m false x final =
      if x < r ∧ final = false then invSqrt r else 0 := by
  rw [generated_eq_model r m false x final wordBound]
  by_cases full : r = 2 ^ m
  · subst r
    cases final <;> simp [model, interval, wordBound]
  · have strict : r < 2 ^ m := by omega
    have nonzero : r ≠ 0 := Nat.ne_of_gt positive
    rw [Nat.mod_eq_of_lt strict]
    cases final <;> simp [model, interval, nonzero]

/-- Memory-zero initialization gives zero amplitude to every memory-one terminal basis vector. -/
lemma initialized_memory_zero (r m x : Nat) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (wordBound : x < 2 ^ m) : generated r m false x true = 0 := by
  rw [initialized_amplitude r m x positive fits wordBound true]
  simp

namespace Point.Extension

open Matrix

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- A real one-qubit rotation with its normalization stored in the carrier. -/
structure Rotation where
  c : ℝ
  s : ℝ
  normalized : c ^ 2 + s ^ 2 = 1

def Rotation.inverse (r : Rotation) : Rotation :=
  ⟨r.c, -r.s, by simpa using r.normalized⟩

def rotationMatrix (r : Rotation) : Matrix2 := !![r.c, -r.s; r.s, r.c]

def halfCos (c : ℝ) : ℝ := Real.sqrt ((1 + c) / 2)
def halfSin (c s : ℝ) : ℝ := s / (2 * halfCos c)

/-- Exact signed half angle; no inverse trigonometry or phase ambiguity is used. -/
lemma half_parameters (c s : ℝ) (nonnegative : 0 ≤ c)
    (normalized : c ^ 2 + s ^ 2 = 1) :
    halfCos c ^ 2 + halfSin c s ^ 2 = 1 ∧
    halfCos c ^ 2 - halfSin c s ^ 2 = c ∧
    2 * halfCos c * halfSin c s = s := by
  have positive : 0 < halfCos c := by
    unfold halfCos
    exact Real.sqrt_pos.2 (by positivity)
  have square : halfCos c ^ 2 = (1 + c) / 2 := by
    unfold halfCos
    exact Real.sq_sqrt (by positivity)
  have doubled : 2 * halfCos c * halfSin c s = s := by
    unfold halfSin
    field_simp [ne_of_gt positive]
  have halfNorm : halfCos c ^ 2 + halfSin c s ^ 2 = 1 := by
    unfold halfSin
    field_simp [ne_of_gt positive]
    nlinarith [normalized, square]
  exact ⟨halfNorm, by nlinarith [halfNorm, square], doubled⟩

def Rotation.half (r : Rotation) (nonnegative : 0 ≤ r.c) : Rotation :=
  ⟨halfCos r.c, halfSin r.c r.s,
    (half_parameters r.c r.s nonnegative r.normalized).1⟩

/-- The fixed nonnegative two-column coefficients. -/
structure Coefficients where
  a : ℝ
  b : ℝ
  a_nonnegative : 0 ≤ a
  b_nonnegative : 0 ≤ b
  normalized : 2 * a ^ 2 + b ^ 2 = 1

def Coefficients.d (p : Coefficients) : ℝ := Real.sqrt (p.a ^ 2 + p.b ^ 2)

lemma Coefficients.d_positive (p : Coefficients) : 0 < p.d := by
  apply Real.sqrt_pos.2
  nlinarith [p.normalized, sq_nonneg p.a, sq_nonneg p.b]

lemma Coefficients.d_square (p : Coefficients) : p.d ^ 2 = p.a ^ 2 + p.b ^ 2 :=
  Real.sq_sqrt (by positivity)

def Coefficients.first (p : Coefficients) : Rotation :=
  ⟨p.a, p.d, by rw [p.d_square]; nlinarith [p.normalized]⟩

lemma Coefficients.first_nonnegative (p : Coefficients) : 0 ≤ p.first.c :=
  p.a_nonnegative

def Coefficients.second (p : Coefficients) : Rotation :=
  ⟨p.a / p.d, -(p.b / p.d), by
    field_simp [ne_of_gt p.d_positive]
    nlinarith [p.d_square]⟩

lemma Coefficients.second_nonnegative (p : Coefficients) : 0 ≤ p.second.c :=
  div_nonneg p.a_nonnegative p.d_positive.le

/-- Explicit one-qubit placements in the `(emitted, memory)` basis order. -/
def onFirst (u : Matrix2) : Matrix4 :=
  !![u 0 0, 0, u 0 1, 0;
     0, u 0 0, 0, u 0 1;
     u 1 0, 0, u 1 1, 0;
     0, u 1 0, 0, u 1 1]

def onSecond (u : Matrix2) : Matrix4 :=
  !![u 0 0, u 0 1, 0, 0;
     u 1 0, u 1 1, 0, 0;
     0, 0, u 0 0, u 0 1;
     0, 0, u 1 0, u 1 1]

def xMatrix : Matrix2 := !![0, 1; 1, 0]
def hMatrix : Matrix2 :=
  let z := (Real.sqrt 2)⁻¹
  !![z, z; z, -z]

def cxFirst : Matrix4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
def cxSecond : Matrix4 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]

/-- Only one-qubit gates and directed CNOTs occur in an actual gate list. -/
inductive Gate where
  | rotate (target : Bool) (r : Rotation)
  | x (target : Bool)
  | hadamard (target : Bool)
  | cnot (control : Bool)

def Gate.matrix : Gate → Matrix4
  | .rotate target r => if target then onSecond (rotationMatrix r) else onFirst (rotationMatrix r)
  | .x target => if target then onSecond xMatrix else onFirst xMatrix
  | .hadamard target => if target then onSecond hMatrix else onFirst hMatrix
  | .cnot control => if control then cxSecond else cxFirst

def Gate.isCnot : Gate → Bool
  | .cnot _ => true
  | _ => false

/-- Lists are chronological: the head gate acts first on a column vector. -/
def run : List Gate → Matrix4
  | [] => 1
  | g :: gs => run gs * g.matrix

def oneQubitCount (gates : List Gate) : Nat := (gates.filter fun g => !g.isCnot).length
def cnotCount (gates : List Gate) : Nat := (gates.filter Gate.isCnot).length

lemma run_append (first second : List Gate) :
    run (first ++ second) = run second * run first := by
  induction first with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, Matrix.mul_assoc]

/-- Both inverse identities are kept explicitly before complexification. -/
def Orthogonal {n : Nat} (u : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  u.transpose * u = 1 ∧ u * u.transpose = 1

lemma orthogonal_mul {n : Nat} {u v : Matrix (Fin n) (Fin n) ℝ}
    (hu : Orthogonal u) (hv : Orthogonal v) : Orthogonal (u * v) := by
  constructor
  · calc
      (u * v).transpose * (u * v) = v.transpose * (u.transpose * u) * v := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hu.1, Matrix.mul_one, hv.1]
  · calc
      (u * v) * (u * v).transpose = u * (v * v.transpose) * u.transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hv.2, Matrix.mul_one, hu.2]

lemma rotation_orthogonal (r : Rotation) : Orthogonal (rotationMatrix r) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [r.normalized]

lemma placement_orthogonal (u : Matrix2) (hu : Orthogonal u) (target : Bool) :
    Orthogonal (if target then onSecond u else onFirst u) := by
  have left (i j : Fin 2) := congrFun (congrFun hu.1 i) j
  have right (i j : Fin 2) := congrFun (congrFun hu.2 i) j
  have l00 := left 0 0
  have l01 := left 0 1
  have l10 := left 1 0
  have l11 := left 1 1
  have r00 := right 0 0
  have r01 := right 0 1
  have r10 := right 1 0
  have r11 := right 1 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at l00 l01 l10 l11 r00 r01 r10 r11
  cases target <;> constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [onFirst, onSecond, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    assumption

lemma x_orthogonal : Orthogonal xMatrix := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [xMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

lemma h_orthogonal : Orthogonal hMatrix := by
  have square : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have positive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [hMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt positive] <;> nlinarith [square]

lemma gate_orthogonal (g : Gate) : Orthogonal g.matrix := by
  cases g with
  | rotate target r => exact placement_orthogonal _ (rotation_orthogonal r) target
  | x target => exact placement_orthogonal _ x_orthogonal target
  | hadamard target => exact placement_orthogonal _ h_orthogonal target
  | cnot control =>
      cases control <;> constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [Gate.matrix, cxFirst, cxSecond, Matrix.mul_apply, Fin.sum_univ_succ]

lemma run_orthogonal (gates : List Gate) : Orthogonal (run gates) := by
  induction gates with
  | nil => simp [run, Orthogonal]
  | cons g gs ih => exact orthogonal_mul ih (gate_orthogonal g)

def complexify {n : Nat} (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  u.map Complex.ofRealHom

lemma complexify_conjTranspose {n : Nat} (u : Matrix (Fin n) (Fin n) ℝ) :
    (complexify u).conjTranspose = complexify u.transpose := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

/-- Every gate list denotes an actual complex unitary, with exact phase. -/
lemma run_unitary (gates : List Gate) :
    (complexify (run gates)).conjTranspose * complexify (run gates) = 1 ∧
    complexify (run gates) * (complexify (run gates)).conjTranspose = 1 := by
  have h := run_orthogonal gates
  rw [complexify_conjTranspose]
  constructor
  · rw [complexify, complexify, ← Matrix.map_mul, h.1]
    simp
  · rw [complexify, complexify, ← Matrix.map_mul, h.2]
    simp

/-- A controlled rotation is four paid native gates, with the rightmost factor acting first. -/
def controlledGates (control : Bool) (r : Rotation) (nonnegative : 0 ≤ r.c) : List Gate :=
  let half := r.half nonnegative
  [.rotate (!control) half, .cnot control, .rotate (!control) half.inverse, .cnot control]

/-- A semantic comparison matrix, not an additional primitive gate. -/
def controlledMatrix (control : Bool) (r : Rotation) : Matrix4 :=
  if control then
    !![1, 0, 0, 0; 0, r.c, 0, -r.s; 0, 0, 1, 0; 0, r.s, 0, r.c]
  else
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, r.c, -r.s; 0, 0, r.s, r.c]

lemma controlledGates_run (control : Bool) (r : Rotation) (nonnegative : 0 ≤ r.c) :
    run (controlledGates control r nonnegative) = controlledMatrix control r := by
  rcases half_parameters r.c r.s nonnegative r.normalized with ⟨norm, difference, product⟩
  cases control <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [controlledGates, controlledMatrix, run, Gate.matrix, onFirst, onSecond,
      rotationMatrix, Rotation.half, Rotation.inverse, cxFirst, cxSecond,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [norm, difference, product]

def lowGates (p : Coefficients) : List Gate :=
  controlledGates true p.first p.first_nonnegative ++
    controlledGates false p.second p.second_nonnegative

def highGates (p : Coefficients) : List Gate :=
  ([.x true] ++ lowGates p) ++ [.x false, .x true]

/-- An explicit orthogonal completion of the prescribed low-cut columns. -/
def lowMatrix (p : Coefficients) : Matrix4 :=
  !![1, 0, 0, 0;
     0, p.a, 0, -p.d;
     0, p.b, p.a / p.d, p.a * p.b / p.d;
     0, p.a, -p.b / p.d, p.a ^ 2 / p.d]

/-- Conjugating the low completion by X placements gives the prescribed high columns. -/
def highMatrix (p : Coefficients) : Matrix4 :=
  !![p.a, 0, p.a ^ 2 / p.d, -p.b / p.d;
     p.b, 0, p.a * p.b / p.d, p.a / p.d;
     p.a, 0, -p.d, 0;
     0, 1, 0, 0]

lemma lowGates_run (p : Coefficients) : run (lowGates p) = lowMatrix p := by
  rw [lowGates, run_append, controlledGates_run, controlledGates_run]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controlledMatrix, Coefficients.first, Coefficients.second, lowMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt p.d_positive]

lemma highGates_run (p : Coefficients) : run (highGates p) = highMatrix p := by
  rw [highGates, run_append, run_append, lowGates_run]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [run, Gate.matrix, onFirst, onSecond, xMatrix, lowMatrix, highMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The displayed 4x4 completions are complex unitaries for every normalized coefficient pair. -/
lemma completions_unitary (p : Coefficients) :
    let low := complexify (lowMatrix p)
    let high := complexify (highMatrix p)
    low.conjTranspose * low = 1 ∧ low * low.conjTranspose = 1 ∧
    high.conjTranspose * high = 1 ∧ high * high.conjTranspose = 1 := by
  have low := run_unitary (lowGates p)
  have high := run_unitary (highGates p)
  rw [lowGates_run] at low
  rw [highGates_run] at high
  exact ⟨low.1, low.2, high.1, high.2⟩

lemma native_gate_counts (p : Coefficients) :
    oneQubitCount (lowGates p) = 4 ∧ cnotCount (lowGates p) = 4 ∧
    oneQubitCount (highGates p) = 7 ∧ cnotCount (highGates p) = 4 ∧
    (lowGates p).length = 8 ∧ (highGates p).length = 11 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Convert row bits into the prescribed 00,01,10,11 order. -/
def index (emitted memory : Bool) : Fin 4 :=
  if emitted then if memory then 3 else 2 else if memory then 1 else 0

lemma low_columns (p : Coefficients) (input emitted memory : Bool) :
    run (lowGates p) (index emitted memory) (index false input) =
      if input then
        if emitted then if memory then p.a else p.b else if memory then p.a else 0
      else if emitted = false ∧ memory = false then 1 else 0 := by
  rw [lowGates_run]
  cases input <;> cases emitted <;> cases memory <;> rfl

lemma high_columns (p : Coefficients) (input emitted memory : Bool) :
    run (highGates p) (index emitted memory) (index false input) =
      if input then if emitted = true ∧ memory = true then 1 else 0
      else if emitted then if memory then 0 else p.a else if memory then p.b else p.a := by
  rw [highGates_run]
  cases input <;> cases emitted <;> cases memory <;> rfl

/-- Squared coefficients in the exact nonnegative normalization convention. -/
lemma weight_square (total part : Nat) :
    weight total part ^ 2 = (part : ℝ) / (total : ℝ) := by
  rw [weight_eq_sqrt_ratio, Real.sq_sqrt (by positivity)]

lemma weight_nonnegative (total part : Nat) : 0 ≤ weight total part := by
  unfold weight invSqrt
  positivity

def lowCoefficients (half cut : Nat) (low : cut < half) : Coefficients where
  a := weight (2 * half - cut) (half - cut)
  b := weight (2 * half - cut) cut
  a_nonnegative := weight_nonnegative _ _
  b_nonnegative := weight_nonnegative _ _
  normalized := by
    rw [weight_square, weight_square]
    have nonzero : ((2 * half - cut : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : (2 * half - cut : Nat) ≠ 0)
    field_simp [nonzero]
    exact_mod_cast (by omega : 2 * (half - cut) + cut = 2 * half - cut)

def highCoefficients (half cut : Nat) (high : half < cut) (bound : cut < 2 * half) :
    Coefficients where
  a := weight cut (cut - half)
  b := weight cut (2 * half - cut)
  a_nonnegative := weight_nonnegative _ _
  b_nonnegative := weight_nonnegative _ _
  normalized := by
    rw [weight_square, weight_square]
    have nonzero : (cut : ℝ) ≠ 0 := by exact_mod_cast (by omega : cut ≠ 0)
    field_simp [nonzero]
    exact_mod_cast (by omega : 2 * (cut - half) + (2 * half - cut) = cut)

/-- The actual list for every legal table branch, including both endpoint cuts. -/
def fixedGates (half cut : Nat) (bound : cut < 2 * half) : List Gate :=
  if zero : cut = 0 then [.hadamard false]
  else if middle : cut = half then [.cnot true, .cnot false]
  else if low : cut < half then lowGates (lowCoefficients half cut low)
  else highGates (highCoefficients half cut (by omega) bound)

/-- The constructed gate list has exactly the frozen table on a fresh emitted/control zero bit. -/
lemma fixed_columns (half cut : Nat) (positive : 0 < half) (bound : cut < 2 * half)
    (input emitted memory : Bool) :
    run (fixedGates half cut bound) (index emitted memory) (index false input) =
      table half cut input emitted memory := by
  unfold fixedGates
  split_ifs with zero middle low
  · subst cut
    cases input <;> cases emitted <;> cases memory <;>
      simp [run, Gate.matrix, onFirst, hMatrix, index, table, weight_double half positive]
  · subst cut
    have nonzero : half ≠ 0 := Nat.ne_of_gt positive
    cases input <;> cases emitted <;> cases memory <;>
      norm_num [run, Gate.matrix, cxFirst, cxSecond, index, table, nonzero,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> rfl
  · rw [low_columns]
    simp [table, zero, middle, low, lowCoefficients]
  · rw [high_columns]
    simp [table, zero, middle, low, highCoefficients]

/-- Exact one-qubit and CNOT counts, without treating controlled rotations as primitive gates. -/
lemma fixed_gate_counts (half cut : Nat) (bound : cut < 2 * half) :
    (oneQubitCount (fixedGates half cut bound),
      cnotCount (fixedGates half cut bound)) =
      if cut = 0 then (1, 0) else if cut = half then (0, 2)
      else if cut < half then (4, 4) else (7, 4) := by
  unfold fixedGates
  split_ifs <;> rfl

/-- Complexification preserves the entire extension, not merely the real prepared columns. -/
lemma fixed_unitary (half cut : Nat) (bound : cut < 2 * half) :
    let u := complexify (run (fixedGates half cut bound))
    u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1 :=
  run_unitary (fixedGates half cut bound)

/-- The physical fresh-control columns agree exactly, including their global phase. -/
lemma fixed_complex_columns (half cut : Nat) (positive : 0 < half) (bound : cut < 2 * half)
    (input emitted memory : Bool) :
    complexify (run (fixedGates half cut bound))
      (index emitted memory) (index false input) = (table half cut input emitted memory : ℂ) :=
  congrArg (fun x : ℝ => (x : ℂ)) (fixed_columns half cut positive bound input emitted memory)

end Point.Extension


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Program

open QuantumAlg
open Matrix

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Physical wire zero emits the next big-endian bit; wire one is the persistent memory. -/
abbrev layout : QuantumLayout 2 :=
  (QuantumSignature.qubits 2).canonicalPlacement.layout

private lemma real_unitary {n : Nat} (u : Matrix (Fin n) (Fin n) ℝ)
    (unitary : Recovery.Point.Extension.Orthogonal u) :
    Recovery.Point.Extension.complexify u ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose, Recovery.Point.Extension.complexify_conjTranspose]
  rw [Recovery.Point.Extension.complexify, Recovery.Point.Extension.complexify, ←
    Matrix.map_mul, unitary.1]
  simp

/-- A native one-qubit token carries precisely the certified matrix used in the accepted list. -/
def oneOperator (u : Recovery.Point.Extension.Matrix2)
    (unitary : Recovery.Point.Extension.Orthogonal u) :
    UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix (Recovery.Point.Extension.complexify u) (real_unitary u unitary)

def single (target : Bool) (u : Recovery.Point.Extension.Matrix2) (unitary :
  Recovery.Point.Extension.Orthogonal u) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  QuantumAlg.Gate.singleQubitAt layout .empty (oneOperator u unitary)
    (if target then 1 else 0) rfl

/-- Both directed CNOTs retain their real original control/target physical wire arguments. -/
def cnot (control : Bool) : UnitaryCircuit AlgorithmGate.model .empty layout :=
  if control then
    (QubitPrimitive.cnot 1 0 (by decide) : QubitPrimitive 2).circuit
      (QubitLayout.canonical 2) .empty
  else
    (QubitPrimitive.cnot 0 1 (by decide) : QubitPrimitive 2).circuit
      (QubitLayout.canonical 2) .empty

def gate : Recovery.Point.Extension.Gate → UnitaryCircuit AlgorithmGate.model .empty layout
  | .rotate target r => single target (Recovery.Point.Extension.rotationMatrix r)
      (Recovery.Point.Extension.rotation_orthogonal r)
  | .x target =>
      single target Recovery.Point.Extension.xMatrix Recovery.Point.Extension.x_orthogonal
  | .hadamard target =>
      single target Recovery.Point.Extension.hMatrix Recovery.Point.Extension.h_orthogonal
  | .cnot control => cnot control

/-- Compile the already accepted chronological list using only native leaves and sequence. -/
def program : List Recovery.Point.Extension.Gate → UnitaryCircuit AlgorithmGate.model .empty layout
  | [] => .identity _ _ _
  | g :: gs => (gate g).seq (program gs)

private lemma single_operator (target : Bool) (u : Recovery.Point.Extension.Matrix2)
    (unitary : Recovery.Point.Extension.Orthogonal u) :
    ((single target u unitary).binaryMatrix environment) =
      if target then (1 : UnitaryOperator (Qubits 1)).tensor (oneOperator u unitary)
      else (oneOperator u unitary).tensor (1 : UnitaryOperator (Qubits 1)) := by
  cases target with
  | false => exact QuantumAlg.Gate.singleQubitAt_first_binaryMatrix .empty 1 _ environment
  | true => exact QuantumAlg.Gate.singleQubitAt_last_binaryMatrix .empty 1 _ environment

private lemma single_matrix (target : Bool) (u : Recovery.Point.Extension.Matrix2)
    (unitary : Recovery.Point.Extension.Orthogonal u) :
    (((single target u unitary).binaryMatrix environment) : HilbertOperator (Qubits 2)) =
      Recovery.Point.Extension.complexify
        (if target then Recovery.Point.Extension.onSecond u else
          Recovery.Point.Extension.onFirst u) := by
  rw [single_operator]
  cases target
  · simp only [Bool.false_eq_true, if_false]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [UnitaryOperator.tensor_apply, prodEquiv, finProdFinEquiv,
        Fin.divNat, Fin.modNat, oneOperator,
        Recovery.Point.Extension.complexify, Recovery.Point.Extension.onFirst]
  · simp only [if_true]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [UnitaryOperator.tensor_apply, prodEquiv, finProdFinEquiv,
        Fin.divNat, Fin.modNat, oneOperator,
        Recovery.Point.Extension.complexify, Recovery.Point.Extension.onSecond]

private lemma cnot_matrix (control : Bool) :
    (((cnot control).binaryMatrix environment) : HilbertOperator (Qubits 2)) =
      Recovery.Point.Extension.complexify
        (if control then Recovery.Point.Extension.cxSecond else
          Recovery.Point.Extension.cxFirst) := by
  cases control <;> simp only [cnot, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [QubitPrimitive.circuit_canonical_binaryMatrix]
  all_goals
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [QubitPrimitive.operator, UnitaryOperator.ofPerm, UnitaryOperator.ofMatrix,
        QubitPrimitive.perm, WireAddress.cnotPerm, WireAddress.cnotMap,
        WireAddress.flipBit, WireAddress.bitIndex, Equiv.Perm.permMatrix,
        Recovery.Point.Extension.complexify, Recovery.Point.Extension.cxFirst,
          Recovery.Point.Extension.cxSecond] <;> decide

/-- Every real native leaf agrees with its accepted local matrix, with exact phase. -/
lemma gate_matrix (g : Recovery.Point.Extension.Gate) :
    (((gate g).binaryMatrix environment) : HilbertOperator (Qubits 2)) =
      Recovery.Point.Extension.complexify g.matrix := by
  cases g with
  | rotate target r => exact single_matrix target _ _
  | x target => exact single_matrix target _ _
  | hadamard target => exact single_matrix target _ _
  | cnot control => exact cnot_matrix control

/-- The same native AST has exactly the accepted complete 4x4 operator. -/
lemma program_matrix (gates : List Recovery.Point.Extension.Gate) :
    (((program gates).binaryMatrix environment) : HilbertOperator (Qubits 2)) =
      Recovery.Point.Extension.complexify (Recovery.Point.Extension.run gates) := by
  induction gates with
  | nil => simp [program, Recovery.Point.Extension.run, Recovery.Point.Extension.complexify,
      UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
  | cons g gs ih =>
      rw [program, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
      change (((program gs).binaryMatrix environment) : HilbertOperator (Qubits 2)) *
          (((gate g).binaryMatrix environment) : HilbertOperator (Qubits 2)) = _
      rw [ih, gate_matrix]
      exact (Matrix.map_mul (f := Complex.ofRealHom)).symm

def event (g : Recovery.Point.Extension.Gate) :
    Resource.Event (.quantum AlgorithmGate.model .empty) :=
  if g.isCnot then .gate AlgorithmGate.Coordinate.cnot
  else .gate AlgorithmGate.Coordinate.singleQubit

private lemma gate_trace (g : Recovery.Point.Extension.Gate) :
    (gate g).eventTrace = [event g] := by
  cases g with
  | rotate target r => rfl
  | x target => rfl
  | hadamard target => rfl
  | cnot control => cases control <;> rfl

/-- Ordered native events are derived from the actual construction, including every rotation. -/
lemma program_trace (gates : List Recovery.Point.Extension.Gate) :
    (program gates).eventTrace = gates.map event := by
  induction gates with
  | nil => rfl
  | cons g gs ih => simp only [program, UnitaryCircuit.seq_eventTrace, gate_trace, ih,
      List.map_cons, List.singleton_append]

private lemma mapped_single_count (gates : List Recovery.Point.Extension.Gate) :
    (gates.map event).count (.gate AlgorithmGate.Coordinate.singleQubit) =
      Recovery.Point.Extension.oneQubitCount gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      cases g <;> simp [event,
        Recovery.Point.Extension.oneQubitCount, Recovery.Point.Extension.Gate.isCnot,
        ih]

private lemma mapped_cnot_count (gates : List Recovery.Point.Extension.Gate) :
    (gates.map event).count (.gate AlgorithmGate.Coordinate.cnot) =
      Recovery.Point.Extension.cnotCount gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      cases g <;> simp [event,
        Recovery.Point.Extension.cnotCount, Recovery.Point.Extension.Gate.isCnot,
        List.filter_cons, ih]

/-- Native one-qubit/CNOT counts come from this program's own event ledger. -/
lemma program_counts (gates : List Recovery.Point.Extension.Gate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.singleQubit) (program gates).eventCost =
        Recovery.Point.Extension.oneQubitCount gates ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.cnot) (program gates).eventCost =
        Recovery.Point.Extension.cnotCount gates := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_trace]
  exact ⟨(ResourcePool.count_ofList _ _).trans (mapped_single_count gates),
    (ResourcePool.count_ofList _ _).trans (mapped_cnot_count gates)⟩

private lemma gate_depth (g : Recovery.Point.Extension.Gate) :
    (gate g).evaluatedEventDepth (fun _ => 1) = 1 := by
  cases g with
  | rotate target r => rfl
  | x target => rfl
  | hadamard target => rfl
  | cnot control => cases control <;> rfl

/-- This serial AST's own structural depth is its list length. -/
lemma program_depth (gates : List Recovery.Point.Extension.Gate) :
    (program gates).evaluatedEventDepth (fun _ => 1) = gates.length := by
  induction gates with
  | nil => rfl
  | cons g gs ih => simp [program, gate_depth, ih, Nat.add_comm]

/-- The unitary word occupies its full two-wire interface and allocates no additional work. -/
lemma program_space (gates : List Recovery.Point.Extension.Gate) :
    (program gates).interfaceSpaceFlow.peakResidentSpace = SpacePool.ofQuantumLayout layout ∧
    (program gates).interfaceSpaceFlow.peakAuxiliarySpace = 0 := by
  simp

/-- Concrete fresh-control columns coincide with the original fixed streaming table. -/
lemma fixed_native_columns (half cut : Nat) (positive : 0 < half) (bound : cut < 2 * half)
    (input emitted memory : Bool) :
    ((program (Recovery.Point.Extension.fixedGates half cut bound)).binaryMatrix environment)
      (Recovery.Point.Extension.index emitted memory) (Recovery.Point.Extension.index false input) =
        (table half cut input emitted memory : ℂ) := by
  rw [show ((program (Recovery.Point.Extension.fixedGates half cut bound)).binaryMatrix environment)
      (Recovery.Point.Extension.index emitted memory) (Recovery.Point.Extension.index false input) =
      Recovery.Point.Extension.complexify (Recovery.Point.Extension.run
        (Recovery.Point.Extension.fixedGates half cut bound))
        (Recovery.Point.Extension.index emitted memory) (Recovery.Point.Extension.index false
          input) from
    congrFun (congrFun (program_matrix _) _) _]
  exact Recovery.Point.Extension.fixed_complex_columns half cut positive bound input emitted memory

/-- The independently displayed branch counts are realized by the actual native circuit. -/
lemma fixed_native_counts (half cut : Nat) (bound : cut < 2 * half) :
    (ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.singleQubit)
        (program (Recovery.Point.Extension.fixedGates half cut bound)).eventCost,
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.cnot)
        (program (Recovery.Point.Extension.fixedGates half cut bound)).eventCost) =
      if cut = 0 then (1, 0) else if cut = half then (0, 2)
      else if cut < half then (4, 4) else (7, 4) := by
  rw [(program_counts _).1, (program_counts _).2]
  exact Recovery.Point.Extension.fixed_gate_counts half cut bound


end
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Program

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Program

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Every branching weight uses the nonnegative real square root, including empty parts. -/
lemma weight_nonnegative (total part : Nat) : 0 ≤ weight total part := by
  unfold weight invSqrt
  positivity

/-- One actual two-wire native word at a particular remaining width. -/
def step (r remaining : Nat) :
    QuantumAlg.UnitaryCircuit QuantumAlg.AlgorithmGate.model .empty layout :=
  program (Recovery.Point.Extension.fixedGates (2 ^ remaining) (r % (2 * 2 ^ remaining))
    (Nat.mod_lt r (by positivity)))

/-- Its fresh-emission input columns retain both possible memory inputs. -/
lemma step_columns (r remaining : Nat) (input emitted memory : Bool) :
    ((step r remaining).binaryMatrix environment)
      (Recovery.Point.Extension.index emitted memory) (Recovery.Point.Extension.index false input) =
        (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted memory : ℂ) := by
  exact fixed_native_columns _ _ (by positivity) _ input emitted memory

/-- Contract the actual native-word columns in the original most-significant-bit order.
This retains the final memory coordinate; it is not a measured ECC protocol. -/
def nativeGenerated (r : Nat) : Nat → Bool → Nat → Bool → ℂ
  | 0, input, x, final => if x = 0 ∧ final = input then 1 else 0
  | remaining + 1, input, x, final =>
      let half := 2 ^ remaining
      let emitted := decide (half ≤ x)
      ((step r remaining).binaryMatrix OracleModel.emptyInterpretation)
          (Recovery.Point.Extension.index emitted false) (Recovery.Point.Extension.index false
            input) *
          nativeGenerated r remaining false (x % half) final +
        ((step r remaining).binaryMatrix OracleModel.emptyInterpretation)
          (Recovery.Point.Extension.index emitted true) (Recovery.Point.Extension.index false
            input) *
          nativeGenerated r remaining true (x % half) final

/-- The recursive native matrix contraction is exactly the accepted real table contraction. -/
lemma nativeGenerated_eq_generated (r remaining : Nat) (input : Bool)
    (x : Nat) (final : Bool) :
    nativeGenerated r remaining input x final =
      (generated r remaining input x final : ℂ) := by
  induction remaining generalizing input x final with
  | zero =>
      by_cases same : x = 0 ∧ final = input <;> simp [nativeGenerated, generated, same]
  | succ remaining ih =>
      simp only [nativeGenerated, step_columns, generated, ih,
        Complex.ofReal_add, Complex.ofReal_mul]

/-- Exact joint amplitudes cover every width and both memory inputs, including zero cut. -/
lemma nativeGenerated_eq_model (r remaining : Nat) (input : Bool)
    (x : Nat) (final : Bool) (bound : x < 2 ^ remaining) :
    nativeGenerated r remaining input x final =
      (model (2 ^ remaining) (r % 2 ^ remaining) input x final : ℂ) := by
  rw [nativeGenerated_eq_generated, generated_eq_model r remaining input x final bound]

/-- Legal memory-zero initialization gives the complete uniform interval vector exactly. -/
lemma native_initialized_amplitude (r remaining x : Nat)
    (positive : 0 < r) (fits : r ≤ 2 ^ remaining) (bound : x < 2 ^ remaining)
    (final : Bool) :
    nativeGenerated r remaining false x final =
      if x < r ∧ final = false then (invSqrt r : ℂ) else 0 := by
  rw [nativeGenerated_eq_generated, initialized_amplitude r remaining x positive fits bound]
  split_ifs <;> rfl

/-- Final memory-one amplitudes vanish on the legal domain, also at width zero and r=2^m. -/
lemma native_initialized_memory_zero (r remaining x : Nat)
    (positive : 0 < r) (fits : r ≤ 2 ^ remaining) (bound : x < 2 ^ remaining) :
    nativeGenerated r remaining false x true = 0 := by
  rw [nativeGenerated_eq_generated, initialized_memory_zero r remaining x positive fits bound]
  rfl

/-- The fixed branch depth is paid by the same serial native program. -/
lemma fixed_native_depth (half cut : Nat) (bound : cut < 2 * half) :
    (program (Recovery.Point.Extension.fixedGates half cut bound)).evaluatedEventDepth (fun _ =>
      1) =
      if cut = 0 then 1 else if cut = half then 2 else if cut < half then 8 else 11 := by
  rw [program_depth]
  unfold Recovery.Point.Extension.fixedGates
  split_ifs <;> rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Program
