/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word34Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word34State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word34Step0 :
    word34Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word34State1 := by decide +kernel

private def word34Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word34State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word34Step1 :
    word34Chunk1.foldl (fun acc a => a.applyPacked acc)
      word34State1 = word34State2 := by decide +kernel

private def word34Chunk2 : List Letter := [.h, .s, .h, .s, .s, .h, .t, .h]
private def word34State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word34Step2 :
    word34Chunk2.foldl (fun acc a => a.applyPacked acc)
      word34State2 = word34State3 := by decide +kernel

private def word34Chunk3 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word34State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word34Step3 :
    word34Chunk3.foldl (fun acc a => a.applyPacked acc)
      word34State3 = word34State4 := by decide +kernel

private def word34Chunk4 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word34State5 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word34Step4 :
    word34Chunk4.foldl (fun acc a => a.applyPacked acc)
      word34State4 = word34State5 := by decide +kernel

private def word34Chunk5 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word34State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word34Step5 :
    word34Chunk5.foldl (fun acc a => a.applyPacked acc)
      word34State5 = word34State6 := by decide +kernel

private def word34Chunk6 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word34State7 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word34Step6 :
    word34Chunk6.foldl (fun acc a => a.applyPacked acc)
      word34State6 = word34State7 := by decide +kernel

private def word34Chunk7 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word34State8 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word34Step7 :
    word34Chunk7.foldl (fun acc a => a.applyPacked acc)
      word34State7 = word34State8 := by decide +kernel

private def word34Chunk8 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word34State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word34Step8 :
    word34Chunk8.foldl (fun acc a => a.applyPacked acc)
      word34State8 = word34State9 := by decide +kernel

private def word34Chunk9 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word34State10 : PackedMat2 :=
    ⟨⟨⟨((21 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-31 : Dyadic) * half ^ 7),
        ((-53 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 7),
        ((17 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((59 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((-25 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((101 : Dyadic) * half ^ 7),
        ((5 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word34Step9 :
    word34Chunk9.foldl (fun acc a => a.applyPacked acc)
      word34State9 = word34State10 := by decide +kernel

private def word34Chunk10 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word34State11 : PackedMat2 :=
    ⟨⟨⟨((127 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((-141 : Dyadic) * half ^ 8),
        ((-61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 8)⟩,
       ⟨((-51 : Dyadic) * half ^ 8),
        ((47 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((51 : Dyadic) * half ^ 8),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-141 : Dyadic) * half ^ 8),
        ((-61 : Dyadic) * half ^ 8)⟩,
       ⟨((127 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word34Step10 :
    word34Chunk10.foldl (fun acc a => a.applyPacked acc)
      word34State10 = word34State11 := by decide +kernel

private def word34Chunk11 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word34State12 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 4),
        ((131 : Dyadic) * half ^ 9)⟩,
       ⟨((45 : Dyadic) * half ^ 7),
        ((25 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-91 : Dyadic) * half ^ 8),
        ((-65 : Dyadic) * half ^ 8)⟩,
       ⟨((67 : Dyadic) * half ^ 7),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-141 : Dyadic) * half ^ 8),
        ((43 : Dyadic) * half ^ 9)⟩,
       ⟨((11 : Dyadic) * half ^ 8),
        ((-225 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 7),
        ((-69 : Dyadic) * half ^ 8)⟩,
       ⟨((-53 : Dyadic) * half ^ 8),
        ((21 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word34Step11 :
    word34Chunk11.foldl (fun acc a => a.applyPacked acc)
      word34State11 = word34State12 := by decide +kernel

private def word34Chunk12 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word34State13 : PackedMat2 :=
    ⟨⟨⟨((-93 : Dyadic) * half ^ 9),
        ((223 : Dyadic) * half ^ 10)⟩,
       ⟨((41 : Dyadic) * half ^ 7),
        ((441 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-87 : Dyadic) * half ^ 8),
        ((-5 : Dyadic) * half ^ 10)⟩,
       ⟨((-195 : Dyadic) * half ^ 9),
        ((269 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((137 : Dyadic) * half ^ 9),
        ((-21 : Dyadic) * half ^ 10)⟩,
       ⟨((33 : Dyadic) * half ^ 7),
        ((-369 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-109 : Dyadic) * half ^ 9),
        ((-257 : Dyadic) * half ^ 10)⟩,
       ⟨((-83 : Dyadic) * half ^ 7),
        ((-71 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word34Step12 :
    word34Chunk12.foldl (fun acc a => a.applyPacked acc)
      word34State12 = word34State13 := by decide +kernel

private def word34Chunk13 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word34State14 : PackedMat2 :=
    ⟨⟨⟨((139 : Dyadic) * half ^ 10),
        ((189 : Dyadic) * half ^ 11)⟩,
       ⟨((31 : Dyadic) * half ^ 6),
        ((-411 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-281 : Dyadic) * half ^ 10),
        ((309 : Dyadic) * half ^ 11)⟩,
       ⟨((-347 : Dyadic) * half ^ 9),
        ((-381 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-281 : Dyadic) * half ^ 10),
        ((309 : Dyadic) * half ^ 11)⟩,
       ⟨((347 : Dyadic) * half ^ 9),
        ((381 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-139 : Dyadic) * half ^ 10),
        ((-189 : Dyadic) * half ^ 11)⟩,
       ⟨((31 : Dyadic) * half ^ 6),
        ((-411 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word34Step13 :
    word34Chunk13.foldl (fun acc a => a.applyPacked acc)
      word34State13 = word34State14 := by decide +kernel

private def word34Chunk14 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word34State15 : PackedMat2 :=
    ⟨⟨⟨((-789 : Dyadic) * half ^ 11),
        ((-155 : Dyadic) * half ^ 9)⟩,
       ⟨((479 : Dyadic) * half ^ 11),
        ((-717 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-441 : Dyadic) * half ^ 11),
        ((669 : Dyadic) * half ^ 11)⟩,
       ⟨((-377 : Dyadic) * half ^ 11),
        ((-99 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((273 : Dyadic) * half ^ 11),
        ((-409 : Dyadic) * half ^ 11)⟩,
       ⟨((1065 : Dyadic) * half ^ 11),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1337 : Dyadic) * half ^ 11),
        ((155 : Dyadic) * half ^ 11)⟩,
       ⟨((-97 : Dyadic) * half ^ 11),
        ((317 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word34Step14 :
    word34Chunk14.foldl (fun acc a => a.applyPacked acc)
      word34State14 = word34State15 := by decide +kernel

private def word34Chunk15 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word34State16 : PackedMat2 :=
    ⟨⟨⟨((919 : Dyadic) * half ^ 12),
        ((-813 : Dyadic) * half ^ 11)⟩,
       ⟨((-959 : Dyadic) * half ^ 12),
        ((123 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1827 : Dyadic) * half ^ 12),
        ((339 : Dyadic) * half ^ 10)⟩,
       ⟨((891 : Dyadic) * half ^ 12),
        ((-971 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-891 : Dyadic) * half ^ 12),
        ((971 : Dyadic) * half ^ 12)⟩,
       ⟨((-1827 : Dyadic) * half ^ 12),
        ((-339 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-959 : Dyadic) * half ^ 12),
        ((123 : Dyadic) * half ^ 12)⟩,
       ⟨((919 : Dyadic) * half ^ 12),
        ((-813 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word34Step15 :
    word34Chunk15.foldl (fun acc a => a.applyPacked acc)
      word34State15 = word34State16 := by decide +kernel

private def word34Chunk16 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word34State17 : PackedMat2 :=
    ⟨⟨⟨((17 : Dyadic) * half ^ 12),
        ((79 : Dyadic) * half ^ 9)⟩,
       ⟨((195 : Dyadic) * half ^ 11),
        ((-493 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1785 : Dyadic) * half ^ 12),
        ((1859 : Dyadic) * half ^ 13)⟩,
       ⟨((-809 : Dyadic) * half ^ 12),
        ((2227 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1785 : Dyadic) * half ^ 12),
        ((1859 : Dyadic) * half ^ 13)⟩,
       ⟨((809 : Dyadic) * half ^ 12),
        ((-2227 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 12),
        ((-79 : Dyadic) * half ^ 9)⟩,
       ⟨((195 : Dyadic) * half ^ 11),
        ((-493 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word34Step16 :
    word34Chunk16.foldl (fun acc a => a.applyPacked acc)
      word34State16 = word34State17 := by decide +kernel

private def word34Chunk17 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word34State18 : PackedMat2 :=
    ⟨⟨⟨((3503 : Dyadic) * half ^ 12),
        ((-251 : Dyadic) * half ^ 13)⟩,
       ⟨((-2123 : Dyadic) * half ^ 13),
        ((-1707 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1255 : Dyadic) * half ^ 13),
        ((2825 : Dyadic) * half ^ 14)⟩,
       ⟨((-93 : Dyadic) * half ^ 13),
        ((1995 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1255 : Dyadic) * half ^ 13),
        ((-2825 : Dyadic) * half ^ 14)⟩,
       ⟨((-93 : Dyadic) * half ^ 13),
        ((1995 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3503 : Dyadic) * half ^ 12),
        ((-251 : Dyadic) * half ^ 13)⟩,
       ⟨((2123 : Dyadic) * half ^ 13),
        ((1707 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word34Step17 :
    word34Chunk17.foldl (fun acc a => a.applyPacked acc)
      word34State17 = word34State18 := by decide +kernel

private def word34Chunk18 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word34State19 : PackedMat2 :=
    ⟨⟨⟨((-1921 : Dyadic) * half ^ 13),
        ((14207 : Dyadic) * half ^ 15)⟩,
       ⟨((9581 : Dyadic) * half ^ 14),
        ((6447 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3219 : Dyadic) * half ^ 14),
        ((3147 : Dyadic) * half ^ 15)⟩,
       ⟨((1603 : Dyadic) * half ^ 13),
        ((-5401 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2137 : Dyadic) * half ^ 13),
        ((13 : Dyadic) * half ^ 15)⟩,
       ⟨((1127 : Dyadic) * half ^ 14),
        ((-6425 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-485 : Dyadic) * half ^ 11),
        ((13423 : Dyadic) * half ^ 15)⟩,
       ⟨((10327 : Dyadic) * half ^ 14),
        ((5739 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word34Step18 :
    word34Chunk18.foldl (fun acc a => a.applyPacked acc)
      word34State18 = word34State19 := by decide +kernel

private def word34Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word34State20 : PackedMat2 :=
    ⟨⟨⟨((2225 : Dyadic) * half ^ 13),
        ((-7059 : Dyadic) * half ^ 15)⟩,
       ⟨((933 : Dyadic) * half ^ 13),
        ((421 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-3939 : Dyadic) * half ^ 15),
        ((12631 : Dyadic) * half ^ 15)⟩,
       ⟨((8145 : Dyadic) * half ^ 15),
        ((7649 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((8145 : Dyadic) * half ^ 15),
        ((7649 : Dyadic) * half ^ 15)⟩,
       ⟨((-3939 : Dyadic) * half ^ 15),
        ((12631 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-933 : Dyadic) * half ^ 13),
        ((-421 : Dyadic) * half ^ 10)⟩,
       ⟨((-2225 : Dyadic) * half ^ 13),
        ((7059 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word34Step19 :
    word34Chunk19.foldl (fun acc a => a.applyPacked acc)
      word34State19 = word34State20 := by decide +kernel

private def word34Chunk20 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word34State21 : PackedMat2 :=
    ⟨⟨⟨((-12883 : Dyadic) * half ^ 16),
        ((-863 : Dyadic) * half ^ 15)⟩,
       ⟨((16563 : Dyadic) * half ^ 16),
        ((-20257 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-5637 : Dyadic) * half ^ 16),
        ((-16319 : Dyadic) * half ^ 15)⟩,
       ⟨((28727 : Dyadic) * half ^ 16),
        ((4501 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((28137 : Dyadic) * half ^ 16),
        ((-11545 : Dyadic) * half ^ 16)⟩,
       ⟨((37139 : Dyadic) * half ^ 16),
        ((8591 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-21983 : Dyadic) * half ^ 16),
        ((115 : Dyadic) * half ^ 12)⟩,
       ⟨((18531 : Dyadic) * half ^ 16),
        ((-14723 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word34Step20 :
    word34Chunk20.foldl (fun acc a => a.applyPacked acc)
      word34State20 = word34State21 := by decide +kernel

private def word34Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word34State22 : PackedMat2 :=
    ⟨⟨⟨((8107 : Dyadic) * half ^ 17),
        ((-16493 : Dyadic) * half ^ 17)⟩,
       ⟨((9633 : Dyadic) * half ^ 17),
        ((-4629 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-14323 : Dyadic) * half ^ 17),
        ((-40639 : Dyadic) * half ^ 16)⟩,
       ⟨((29731 : Dyadic) * half ^ 17),
        ((-31659 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((29731 : Dyadic) * half ^ 17),
        ((-31659 : Dyadic) * half ^ 17)⟩,
       ⟨((-14323 : Dyadic) * half ^ 17),
        ((-40639 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-9633 : Dyadic) * half ^ 17),
        ((4629 : Dyadic) * half ^ 16)⟩,
       ⟨((-8107 : Dyadic) * half ^ 17),
        ((16493 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word34Step21 :
    word34Chunk21.foldl (fun acc a => a.applyPacked acc)
      word34State21 = word34State22 := by decide +kernel

private def word34Chunk22 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word34State23 : PackedMat2 :=
    ⟨⟨⟨((-46119 : Dyadic) * half ^ 17),
        ((-2331 : Dyadic) * half ^ 17)⟩,
       ⟨((801 : Dyadic) * half ^ 11),
        ((-3641 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-46263 : Dyadic) * half ^ 16),
        ((18099 : Dyadic) * half ^ 18)⟩,
       ⟨((-3231 : Dyadic) * half ^ 13),
        ((-42677 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((46263 : Dyadic) * half ^ 16),
        ((-18099 : Dyadic) * half ^ 18)⟩,
       ⟨((-3231 : Dyadic) * half ^ 13),
        ((-42677 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-46119 : Dyadic) * half ^ 17),
        ((-2331 : Dyadic) * half ^ 17)⟩,
       ⟨((-801 : Dyadic) * half ^ 11),
        ((3641 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word34Step22 :
    word34Chunk22.foldl (fun acc a => a.applyPacked acc)
      word34State22 = word34State23 := by decide +kernel

private def word34Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word34State24 : PackedMat2 :=
    ⟨⟨⟨((-15291 : Dyadic) * half ^ 17),
        ((-37327 : Dyadic) * half ^ 19)⟩,
       ⟨((-119285 : Dyadic) * half ^ 18),
        ((-129175 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((179561 : Dyadic) * half ^ 18),
        ((-113635 : Dyadic) * half ^ 19)⟩,
       ⟨((-21753 : Dyadic) * half ^ 17),
        ((-88591 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((179561 : Dyadic) * half ^ 18),
        ((-113635 : Dyadic) * half ^ 19)⟩,
       ⟨((21753 : Dyadic) * half ^ 17),
        ((88591 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((15291 : Dyadic) * half ^ 17),
        ((37327 : Dyadic) * half ^ 19)⟩,
       ⟨((-119285 : Dyadic) * half ^ 18),
        ((-129175 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word34Step23 :
    word34Chunk23.foldl (fun acc a => a.applyPacked acc)
      word34State23 = word34State24 := by decide +kernel

private def word34Chunk24 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word34State25 : PackedMat2 :=
    ⟨⟨⟨((-19155 : Dyadic) * half ^ 19),
        ((102033 : Dyadic) * half ^ 19)⟩,
       ⟨((-172279 : Dyadic) * half ^ 19),
        ((-26415 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((6561 : Dyadic) * half ^ 18),
        ((149395 : Dyadic) * half ^ 18)⟩,
       ⟨((22523 : Dyadic) * half ^ 18),
        ((-144675 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((22523 : Dyadic) * half ^ 18),
        ((-144675 : Dyadic) * half ^ 19)⟩,
       ⟨((6561 : Dyadic) * half ^ 18),
        ((149395 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((172279 : Dyadic) * half ^ 19),
        ((26415 : Dyadic) * half ^ 19)⟩,
       ⟨((19155 : Dyadic) * half ^ 19),
        ((-102033 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word34Step24 :
    word34Chunk24.foldl (fun acc a => a.applyPacked acc)
      word34State24 = word34State25 := by decide +kernel

private def word34Chunk25 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word34State26 : PackedMat2 :=
    ⟨⟨⟨((-76771 : Dyadic) * half ^ 18),
        ((-62255 : Dyadic) * half ^ 18)⟩,
       ⟨((-38499 : Dyadic) * half ^ 19),
        ((324569 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((524633 : Dyadic) * half ^ 20),
        ((33899 : Dyadic) * half ^ 18)⟩,
       ⟨((456039 : Dyadic) * half ^ 20),
        ((-134437 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((202235 : Dyadic) * half ^ 19),
        ((34297 : Dyadic) * half ^ 20)⟩,
       ⟨((66639 : Dyadic) * half ^ 19),
        ((-15323 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((573589 : Dyadic) * half ^ 20),
        ((115043 : Dyadic) * half ^ 20)⟩,
       ⟨((75549 : Dyadic) * half ^ 20),
        ((-192041 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word34Step25 :
    word34Chunk25.foldl (fun acc a => a.applyPacked acc)
      word34State25 = word34State26 := by decide +kernel

private def word34Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word34State27 : PackedMat2 :=
    ⟨⟨⟨((-1871 : Dyadic) * half ^ 16),
        ((164483 : Dyadic) * half ^ 21)⟩,
       ⟨((69629 : Dyadic) * half ^ 19),
        ((379419 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((20605 : Dyadic) * half ^ 16),
        ((-121817 : Dyadic) * half ^ 19)⟩,
       ⟨((870591 : Dyadic) * half ^ 20),
        ((64743 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((20605 : Dyadic) * half ^ 16),
        ((-121817 : Dyadic) * half ^ 19)⟩,
       ⟨((-870591 : Dyadic) * half ^ 20),
        ((-64743 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1871 : Dyadic) * half ^ 16),
        ((-164483 : Dyadic) * half ^ 21)⟩,
       ⟨((69629 : Dyadic) * half ^ 19),
        ((379419 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word34Step26 :
    word34Chunk26.foldl (fun acc a => a.applyPacked acc)
      word34State26 = word34State27 := by decide +kernel

private def word34Chunk27 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word34State28 : PackedMat2 :=
    ⟨⟨⟨((-828029 : Dyadic) * half ^ 21),
        ((1354267 : Dyadic) * half ^ 22)⟩,
       ⟨((-806417 : Dyadic) * half ^ 21),
        ((-1155079 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((265797 : Dyadic) * half ^ 21),
        ((-127675 : Dyadic) * half ^ 19)⟩,
       ⟨((94665 : Dyadic) * half ^ 19),
        ((304615 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-49265 : Dyadic) * half ^ 20),
        ((-644457 : Dyadic) * half ^ 22)⟩,
       ⟨((559965 : Dyadic) * half ^ 20),
        ((112863 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((49797 : Dyadic) * half ^ 20),
        ((-817223 : Dyadic) * half ^ 21)⟩,
       ⟨((1254673 : Dyadic) * half ^ 21),
        ((-5403 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word34Step27 :
    word34Chunk27.foldl (fun acc a => a.applyPacked acc)
      word34State27 = word34State28 := by decide +kernel

private def word34Chunk28 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word34State29 : PackedMat2 :=
    ⟨⟨⟨((2426481 : Dyadic) * half ^ 22),
        ((-1522379 : Dyadic) * half ^ 23)⟩,
       ⟨((-295221 : Dyadic) * half ^ 19),
        ((-1477027 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-572031 : Dyadic) * half ^ 22),
        ((-2041133 : Dyadic) * half ^ 23)⟩,
       ⟨((42365 : Dyadic) * half ^ 18),
        ((-1419159 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-572031 : Dyadic) * half ^ 22),
        ((-2041133 : Dyadic) * half ^ 23)⟩,
       ⟨((-42365 : Dyadic) * half ^ 18),
        ((1419159 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2426481 : Dyadic) * half ^ 22),
        ((1522379 : Dyadic) * half ^ 23)⟩,
       ⟨((-295221 : Dyadic) * half ^ 19),
        ((-1477027 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word34Step28 :
    word34Chunk28.foldl (fun acc a => a.applyPacked acc)
      word34State28 = word34State29 := by decide +kernel

private def word34Chunk29 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word34State30 : PackedMat2 :=
    ⟨⟨⟨((4915011 : Dyadic) * half ^ 23),
        ((-439095 : Dyadic) * half ^ 22)⟩,
       ⟨((-4686621 : Dyadic) * half ^ 23),
        ((687949 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3497207 : Dyadic) * half ^ 23),
        ((2059167 : Dyadic) * half ^ 23)⟩,
       ⟨((-559925 : Dyadic) * half ^ 23),
        ((-302841 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1453485 : Dyadic) * half ^ 23),
        ((1468641 : Dyadic) * half ^ 23)⟩,
       ⟨((2664849 : Dyadic) * half ^ 23),
        ((1014283 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((190241 : Dyadic) * half ^ 23),
        ((-114195 : Dyadic) * half ^ 23)⟩,
       ⟨((1566139 : Dyadic) * half ^ 23),
        ((-300051 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word34Step29 :
    word34Chunk29.foldl (fun acc a => a.applyPacked acc)
      word34State29 = word34State30 := by decide +kernel

private def word34Chunk30 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word34State31 : PackedMat2 :=
    ⟨⟨⟨((2394129 : Dyadic) * half ^ 24),
        ((2058927 : Dyadic) * half ^ 23)⟩,
       ⟨((452449 : Dyadic) * half ^ 24),
        ((6912129 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((7524939 : Dyadic) * half ^ 24),
        ((-2043629 : Dyadic) * half ^ 24)⟩,
       ⟨((-8997277 : Dyadic) * half ^ 24),
        ((-16617 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((8997277 : Dyadic) * half ^ 24),
        ((16617 : Dyadic) * half ^ 20)⟩,
       ⟨((-7524939 : Dyadic) * half ^ 24),
        ((2043629 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((452449 : Dyadic) * half ^ 24),
        ((6912129 : Dyadic) * half ^ 24)⟩,
       ⟨((2394129 : Dyadic) * half ^ 24),
        ((2058927 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word34Step30 :
    word34Chunk30.foldl (fun acc a => a.applyPacked acc)
      word34State30 = word34State31 := by decide +kernel

private def word34Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word34State32 : PackedMat2 :=
    ⟨⟨⟨((243865 : Dyadic) * half ^ 25),
        ((9869367 : Dyadic) * half ^ 25)⟩,
       ⟨((16956795 : Dyadic) * half ^ 25),
        ((352443 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3693235 : Dyadic) * half ^ 25),
        ((6614179 : Dyadic) * half ^ 24)⟩,
       ⟨((-7073095 : Dyadic) * half ^ 25),
        ((10627235 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-7073095 : Dyadic) * half ^ 25),
        ((10627235 : Dyadic) * half ^ 25)⟩,
       ⟨((3693235 : Dyadic) * half ^ 25),
        ((6614179 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-16956795 : Dyadic) * half ^ 25),
        ((-352443 : Dyadic) * half ^ 23)⟩,
       ⟨((-243865 : Dyadic) * half ^ 25),
        ((-9869367 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word34Step31 :
    word34Chunk31.foldl (fun acc a => a.applyPacked acc)
      word34State31 = word34State32 := by decide +kernel

private def word34Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word34State33 : PackedMat2 :=
    ⟨⟨⟨((-19292051 : Dyadic) * half ^ 25),
        ((-10269391 : Dyadic) * half ^ 26)⟩,
       ⟨((3935543 : Dyadic) * half ^ 24),
        ((-1702623 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-4319677 : Dyadic) * half ^ 25),
        ((33387985 : Dyadic) * half ^ 26)⟩,
       ⟨((-3242293 : Dyadic) * half ^ 24),
        ((6244163 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-13571911 : Dyadic) * half ^ 25),
        ((-2164909 : Dyadic) * half ^ 26)⟩,
       ⟨((9908037 : Dyadic) * half ^ 24),
        ((-10804263 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-535423 : Dyadic) * half ^ 22),
        ((-27163137 : Dyadic) * half ^ 26)⟩,
       ⟨((5986007 : Dyadic) * half ^ 25),
        ((11420965 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word34Step32 :
    word34Chunk32.foldl (fun acc a => a.applyPacked acc)
      word34State32 = word34State33 := by decide +kernel

private def word34Chunk33 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word34State34 : PackedMat2 :=
    ⟨⟨⟨((-443933 : Dyadic) * half ^ 22),
        ((-61076727 : Dyadic) * half ^ 27)⟩,
       ⟨((13752727 : Dyadic) * half ^ 26),
        ((-10933235 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-7682559 : Dyadic) * half ^ 26),
        ((16311099 : Dyadic) * half ^ 27)⟩,
       ⟨((23136395 : Dyadic) * half ^ 25),
        ((-3417793 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((4932223 : Dyadic) * half ^ 25),
        ((-53955349 : Dyadic) * half ^ 27)⟩,
       ⟨((-6446653 : Dyadic) * half ^ 26),
        ((-38590231 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((12535873 : Dyadic) * half ^ 25),
        ((20855655 : Dyadic) * half ^ 27)⟩,
       ⟨((-36004981 : Dyadic) * half ^ 26),
        ((6649799 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word34Step33 :
    word34Chunk33.foldl (fun acc a => a.applyPacked acc)
      word34State33 = word34State34 := by decide +kernel

private def word34Chunk34 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word34State35 : PackedMat2 :=
    ⟨⟨⟨((-6039955 : Dyadic) * half ^ 25),
        ((-69854953 : Dyadic) * half ^ 28)⟩,
       ⟨((-93833991 : Dyadic) * half ^ 27),
        ((22622517 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((16534075 : Dyadic) * half ^ 26),
        ((60075063 : Dyadic) * half ^ 28)⟩,
       ⟨((21672487 : Dyadic) * half ^ 27),
        ((-71588149 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-16534075 : Dyadic) * half ^ 26),
        ((-60075063 : Dyadic) * half ^ 28)⟩,
       ⟨((21672487 : Dyadic) * half ^ 27),
        ((-71588149 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-6039955 : Dyadic) * half ^ 25),
        ((-69854953 : Dyadic) * half ^ 28)⟩,
       ⟨((93833991 : Dyadic) * half ^ 27),
        ((-22622517 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word34Step34 :
    word34Chunk34.foldl (fun acc a => a.applyPacked acc)
      word34State34 = word34State35 := by decide +kernel

private def word34Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word34State36 : PackedMat2 :=
    ⟨⟨⟨((-173954749 : Dyadic) * half ^ 28),
        ((112580337 : Dyadic) * half ^ 29)⟩,
       ⟨((-67436343 : Dyadic) * half ^ 27),
        ((-140074015 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((35071617 : Dyadic) * half ^ 28),
        ((-63809405 : Dyadic) * half ^ 29)⟩,
       ⟨((5263623 : Dyadic) * half ^ 25),
        ((69572437 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((35071617 : Dyadic) * half ^ 28),
        ((-63809405 : Dyadic) * half ^ 29)⟩,
       ⟨((-5263623 : Dyadic) * half ^ 25),
        ((-69572437 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((173954749 : Dyadic) * half ^ 28),
        ((-112580337 : Dyadic) * half ^ 29)⟩,
       ⟨((-67436343 : Dyadic) * half ^ 27),
        ((-140074015 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word34Step35 :
    word34Chunk35.foldl (fun acc a => a.applyPacked acc)
      word34State35 = word34State36 := by decide +kernel

private def word34Chunk36 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word34State37 : PackedMat2 :=
    ⟨⟨⟨((1519877 : Dyadic) * half ^ 24),
        ((119996917 : Dyadic) * half ^ 30)⟩,
       ⟨((23779459 : Dyadic) * half ^ 29),
        ((-717909265 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((17618355 : Dyadic) * half ^ 28),
        ((141436753 : Dyadic) * half ^ 30)⟩,
       ⟨((-76000479 : Dyadic) * half ^ 29),
        ((-82256723 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-17618355 : Dyadic) * half ^ 28),
        ((-141436753 : Dyadic) * half ^ 30)⟩,
       ⟨((-76000479 : Dyadic) * half ^ 29),
        ((-82256723 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((1519877 : Dyadic) * half ^ 24),
        ((119996917 : Dyadic) * half ^ 30)⟩,
       ⟨((-23779459 : Dyadic) * half ^ 29),
        ((717909265 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word34Step36 :
    word34Chunk36.foldl (fun acc a => a.applyPacked acc)
      word34State36 = word34State37 := by decide +kernel

private def word34Chunk37 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word34State38 : PackedMat2 :=
    ⟨⟨⟨((-488415 : Dyadic) * half ^ 25),
        ((175986051 : Dyadic) * half ^ 29)⟩,
       ⟨((-319841593 : Dyadic) * half ^ 29),
        ((63396033 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((636390323 : Dyadic) * half ^ 30),
        ((44396687 : Dyadic) * half ^ 29)⟩,
       ⟨((251936161 : Dyadic) * half ^ 30),
        ((-5186233 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((65141619 : Dyadic) * half ^ 29),
        ((192227081 : Dyadic) * half ^ 30)⟩,
       ⟨((-23651755 : Dyadic) * half ^ 29),
        ((-222081621 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-288576069 : Dyadic) * half ^ 30),
        ((-312026953 : Dyadic) * half ^ 30)⟩,
       ⟨((415368135 : Dyadic) * half ^ 30),
        ((-327656233 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word34Step37 :
    word34Chunk37.foldl (fun acc a => a.applyPacked acc)
      word34State37 = word34State38 := by decide +kernel

private def word34Chunk38 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word34State39 : PackedMat2 :=
    ⟨⟨⟨((1980017713 : Dyadic) * half ^ 31),
        ((9768061 : Dyadic) * half ^ 31)⟩,
       ⟨((-140773375 : Dyadic) * half ^ 31),
        ((-61555305 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-58720133 : Dyadic) * half ^ 31),
        ((325908085 : Dyadic) * half ^ 31)⟩,
       ⟨((-86272591 : Dyadic) * half ^ 31),
        ((3157231 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-86272591 : Dyadic) * half ^ 31),
        ((3157231 : Dyadic) * half ^ 24)⟩,
       ⟨((-58720133 : Dyadic) * half ^ 31),
        ((325908085 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((140773375 : Dyadic) * half ^ 31),
        ((61555305 : Dyadic) * half ^ 29)⟩,
       ⟨((-1980017713 : Dyadic) * half ^ 31),
        ((-9768061 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word34Step38 :
    word34Chunk38.foldl (fun acc a => a.applyPacked acc)
      word34State38 = word34State39 := by decide +kernel

private def word34Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word34State40 : PackedMat2 :=
    ⟨⟨⟨((41046007 : Dyadic) * half ^ 31),
        ((1120007581 : Dyadic) * half ^ 31)⟩,
       ⟨((189385405 : Dyadic) * half ^ 30),
        ((-7313619 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((60262435 : Dyadic) * half ^ 29),
        ((-1523241245 : Dyadic) * half ^ 32)⟩,
       ⟨((128269461 : Dyadic) * half ^ 30),
        ((1159257663 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((181991791 : Dyadic) * half ^ 31),
        ((-248794331 : Dyadic) * half ^ 31)⟩,
       ⟨((670624727 : Dyadic) * half ^ 30),
        ((7744591 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1090753105 : Dyadic) * half ^ 31),
        ((419816817 : Dyadic) * half ^ 32)⟩,
       ⟨((1149262057 : Dyadic) * half ^ 31),
        ((-337724803 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word34Step39 :
    word34Chunk39.foldl (fun acc a => a.applyPacked acc)
      word34State39 = word34State40 := by decide +kernel

private def word34Chunk40 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word34State41 : PackedMat2 :=
    ⟨⟨⟨((911437031 : Dyadic) * half ^ 32),
        ((-3016819675 : Dyadic) * half ^ 33)⟩,
       ⟨((523569439 : Dyadic) * half ^ 30),
        ((2733830113 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-748085011 : Dyadic) * half ^ 32),
        ((768311217 : Dyadic) * half ^ 33)⟩,
       ⟨((237945271 : Dyadic) * half ^ 30),
        ((-2522635049 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-748085011 : Dyadic) * half ^ 32),
        ((768311217 : Dyadic) * half ^ 33)⟩,
       ⟨((-237945271 : Dyadic) * half ^ 30),
        ((2522635049 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-911437031 : Dyadic) * half ^ 32),
        ((3016819675 : Dyadic) * half ^ 33)⟩,
       ⟨((523569439 : Dyadic) * half ^ 30),
        ((2733830113 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word34Step40 :
    word34Chunk40.foldl (fun acc a => a.applyPacked acc)
      word34State40 = word34State41 := by decide +kernel

private def word34Chunk41 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word34State42 : PackedMat2 :=
    ⟨⟨⟨((-5988259347 : Dyadic) * half ^ 33),
        ((-353629989 : Dyadic) * half ^ 33)⟩,
       ⟨((5290740277 : Dyadic) * half ^ 33),
        ((-264065129 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-20987543 : Dyadic) * half ^ 32),
        ((-61851555 : Dyadic) * half ^ 29)⟩,
       ⟨((-197697583 : Dyadic) * half ^ 32),
        ((1927357055 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-197697583 : Dyadic) * half ^ 32),
        ((1927357055 : Dyadic) * half ^ 33)⟩,
       ⟨((-20987543 : Dyadic) * half ^ 32),
        ((-61851555 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-5290740277 : Dyadic) * half ^ 33),
        ((264065129 : Dyadic) * half ^ 33)⟩,
       ⟨((5988259347 : Dyadic) * half ^ 33),
        ((353629989 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word34Step41 :
    word34Chunk41.foldl (fun acc a => a.applyPacked acc)
      word34State41 = word34State42 := by decide +kernel

private def word34Chunk42 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word34State43 : PackedMat2 :=
    ⟨⟨⟨((1534412663 : Dyadic) * half ^ 34),
        ((-8322549005 : Dyadic) * half ^ 34)⟩,
       ⟨((3855259865 : Dyadic) * half ^ 34),
        ((-4777585289 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1112549863 : Dyadic) * half ^ 32),
        ((-1493248869 : Dyadic) * half ^ 34)⟩,
       ⟨((360282941 : Dyadic) * half ^ 30),
        ((2128865201 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-360282941 : Dyadic) * half ^ 30),
        ((-2128865201 : Dyadic) * half ^ 33)⟩,
       ⟨((1112549863 : Dyadic) * half ^ 32),
        ((1493248869 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3855259865 : Dyadic) * half ^ 34),
        ((-4777585289 : Dyadic) * half ^ 34)⟩,
       ⟨((1534412663 : Dyadic) * half ^ 34),
        ((-8322549005 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word34Step42 :
    word34Chunk42.foldl (fun acc a => a.applyPacked acc)
      word34State42 = word34State43 := by decide +kernel

private def word34Chunk43 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word34State44 : PackedMat2 :=
    ⟨⟨⟨((-14735830819 : Dyadic) * half ^ 35),
        ((5284864177 : Dyadic) * half ^ 34)⟩,
       ⟨((-12470957367 : Dyadic) * half ^ 35),
        ((-5960538009 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-12606284659 : Dyadic) * half ^ 35),
        ((-3930344565 : Dyadic) * half ^ 35)⟩,
       ⟨((2530848689 : Dyadic) * half ^ 35),
        ((1574228399 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((8663482627 : Dyadic) * half ^ 35),
        ((-5037717985 : Dyadic) * half ^ 35)⟩,
       ⟨((-16524171757 : Dyadic) * half ^ 35),
        ((-3784283337 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4609190345 : Dyadic) * half ^ 35),
        ((13603394093 : Dyadic) * half ^ 35)⟩,
       ⟨((-16530266363 : Dyadic) * half ^ 35),
        ((566218363 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word34Step43 :
    word34Chunk43.foldl (fun acc a => a.applyPacked acc)
      word34State43 = word34State44 := by decide +kernel

private def word34Chunk44 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word34State45 : PackedMat2 :=
    ⟨⟨⟨((21136948351 : Dyadic) * half ^ 35),
        ((-13813010795 : Dyadic) * half ^ 36)⟩,
       ⟨((-21590539297 : Dyadic) * half ^ 35),
        ((-9469795687 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-3750182041 : Dyadic) * half ^ 34),
        ((-5798358879 : Dyadic) * half ^ 35)⟩,
       ⟨((-1974448319 : Dyadic) * half ^ 35),
        ((-133529575 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3750182041 : Dyadic) * half ^ 34),
        ((5798358879 : Dyadic) * half ^ 35)⟩,
       ⟨((-1974448319 : Dyadic) * half ^ 35),
        ((-133529575 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((21136948351 : Dyadic) * half ^ 35),
        ((-13813010795 : Dyadic) * half ^ 36)⟩,
       ⟨((21590539297 : Dyadic) * half ^ 35),
        ((9469795687 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word34Step44 :
    word34Chunk44.foldl (fun acc a => a.applyPacked acc)
      word34State44 = word34State45 := by decide +kernel

private def word34Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word34State46 : PackedMat2 :=
    ⟨⟨⟨((50132077475 : Dyadic) * half ^ 36),
        ((13245198571 : Dyadic) * half ^ 37)⟩,
       ⟨((-27662887489 : Dyadic) * half ^ 36),
        ((1594225051 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((812381699 : Dyadic) * half ^ 33),
        ((-19524622797 : Dyadic) * half ^ 36)⟩,
       ⟨((-19189923323 : Dyadic) * half ^ 36),
        ((9539519953 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2496275711 : Dyadic) * half ^ 34),
        ((-12690869731 : Dyadic) * half ^ 37)⟩,
       ⟨((-14532071375 : Dyadic) * half ^ 35),
        ((25688976915 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-7419711811 : Dyadic) * half ^ 36),
        ((-11234594993 : Dyadic) * half ^ 36)⟩,
       ⟨((-728185845 : Dyadic) * half ^ 33),
        ((-19448741241 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word34Step45 :
    word34Chunk45.foldl (fun acc a => a.applyPacked acc)
      word34State45 = word34State46 := by decide +kernel

private def word34Chunk46 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word34State47 : PackedMat2 :=
    ⟨⟨⟨((60098009383 : Dyadic) * half ^ 37),
        ((79590889993 : Dyadic) * half ^ 38)⟩,
       ⟨((22613624467 : Dyadic) * half ^ 36),
        ((-3031330813 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-1485069055 : Dyadic) * half ^ 32),
        ((-4486707671 : Dyadic) * half ^ 38)⟩,
       ⟨((75710170973 : Dyadic) * half ^ 37),
        ((-64183893669 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-29848592999 : Dyadic) * half ^ 37),
        ((123232380733 : Dyadic) * half ^ 38)⟩,
       ⟨((-17167650335 : Dyadic) * half ^ 36),
        ((28187961213 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((41311110403 : Dyadic) * half ^ 37),
        ((14870760449 : Dyadic) * half ^ 38)⟩,
       ⟨((-19139889795 : Dyadic) * half ^ 36),
        ((-105325258317 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word34Step46 :
    word34Chunk46.foldl (fun acc a => a.applyPacked acc)
      word34State46 = word34State47 := by decide +kernel

private def word34Chunk47 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word34State48 : PackedMat2 :=
    ⟨⟨⟨((11696023059 : Dyadic) * half ^ 38),
        ((-7867043275 : Dyadic) * half ^ 35)⟩,
       ⟨((5628330279 : Dyadic) * half ^ 38),
        ((45865192863 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-10891654287 : Dyadic) * half ^ 36),
        ((-12882612145 : Dyadic) * half ^ 37)⟩,
       ⟨((-108832845393 : Dyadic) * half ^ 37),
        ((4147128609 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-29912352899 : Dyadic) * half ^ 38),
        ((87049536819 : Dyadic) * half ^ 38)⟩,
       ⟨((21618095681 : Dyadic) * half ^ 38),
        ((130616153967 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((77333365963 : Dyadic) * half ^ 37),
        ((-1516923195 : Dyadic) * half ^ 37)⟩,
       ⟨((14397019763 : Dyadic) * half ^ 37),
        ((8662176669 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word34Step47 :
    word34Chunk47.foldl (fun acc a => a.applyPacked acc)
      word34State47 = word34State48 := by decide +kernel

private def word34Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word34State49 : PackedMat2 :=
    ⟨⟨⟨((-87934405531 : Dyadic) * half ^ 39),
        ((-54269138377 : Dyadic) * half ^ 39)⟩,
       ⟨((-22508896275 : Dyadic) * half ^ 39),
        ((-3322555457 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((177831265265 : Dyadic) * half ^ 39),
        ((-110650091957 : Dyadic) * half ^ 39)⟩,
       ⟨((-40900690209 : Dyadic) * half ^ 39),
        ((-167580650401 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-40900690209 : Dyadic) * half ^ 39),
        ((-167580650401 : Dyadic) * half ^ 38)⟩,
       ⟨((177831265265 : Dyadic) * half ^ 39),
        ((-110650091957 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((22508896275 : Dyadic) * half ^ 39),
        ((3322555457 : Dyadic) * half ^ 35)⟩,
       ⟨((87934405531 : Dyadic) * half ^ 39),
        ((54269138377 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word34Step48 :
    word34Chunk48.foldl (fun acc a => a.applyPacked acc)
      word34State48 = word34State49 := by decide +kernel

private def word34Chunk49 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word34State50 : PackedMat2 :=
    ⟨⟨⟨((-77635147331 : Dyadic) * half ^ 38),
        ((-36034873989 : Dyadic) * half ^ 38)⟩,
       ⟨((-320033786457 : Dyadic) * half ^ 39),
        ((-2078186781 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-90753872385 : Dyadic) * half ^ 39),
        ((480279811439 : Dyadic) * half ^ 40)⟩,
       ⟨((-192530655325 : Dyadic) * half ^ 39),
        ((-96329131263 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-23996917511 : Dyadic) * half ^ 36),
        ((141642263855 : Dyadic) * half ^ 39)⟩,
       ⟨((-288304471351 : Dyadic) * half ^ 39),
        ((-25444195735 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-19056530385 : Dyadic) * half ^ 37),
        ((-475304081119 : Dyadic) * half ^ 40)⟩,
       ⟨((-4244585901 : Dyadic) * half ^ 35),
        ((164763491795 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word34Step49 :
    word34Chunk49.foldl (fun acc a => a.applyPacked acc)
      word34State49 = word34State50 := by decide +kernel

private def word34Chunk50 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word34State51 : PackedMat2 :=
    ⟨⟨⟨((188420920803 : Dyadic) * half ^ 39),
        ((-509354047011 : Dyadic) * half ^ 41)⟩,
       ⟨((-599366046791 : Dyadic) * half ^ 40),
        ((-33931207165 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((90416374361 : Dyadic) * half ^ 38),
        ((128560923197 : Dyadic) * half ^ 41)⟩,
       ⟨((-647815120601 : Dyadic) * half ^ 40),
        ((-193130183883 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((40211388385 : Dyadic) * half ^ 38),
        ((1009480618045 : Dyadic) * half ^ 41)⟩,
       ⟨((32284630343 : Dyadic) * half ^ 40),
        ((286149623157 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((237711419923 : Dyadic) * half ^ 40),
        ((-976207888397 : Dyadic) * half ^ 41)⟩,
       ⟨((-16977664193 : Dyadic) * half ^ 36),
        ((-222524205185 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word34Step50 :
    word34Chunk50.foldl (fun acc a => a.applyPacked acc)
      word34State50 = word34State51 := by decide +kernel

private def word34Chunk51 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word34State52 : PackedMat2 :=
    ⟨⟨⟨((417700834875 : Dyadic) * half ^ 40),
        ((467831070115 : Dyadic) * half ^ 42)⟩,
       ⟨((-524845325465 : Dyadic) * half ^ 41),
        ((-129551936551 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((528633698709 : Dyadic) * half ^ 40),
        ((609498177635 : Dyadic) * half ^ 42)⟩,
       ⟨((-1469390438285 : Dyadic) * half ^ 41),
        ((750803944747 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-528633698709 : Dyadic) * half ^ 40),
        ((-609498177635 : Dyadic) * half ^ 42)⟩,
       ⟨((-1469390438285 : Dyadic) * half ^ 41),
        ((750803944747 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((417700834875 : Dyadic) * half ^ 40),
        ((467831070115 : Dyadic) * half ^ 42)⟩,
       ⟨((524845325465 : Dyadic) * half ^ 41),
        ((129551936551 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word34Step51 :
    word34Chunk51.foldl (fun acc a => a.applyPacked acc)
      word34State51 = word34State52 := by decide +kernel

private def word34Chunk52 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word34State53 : PackedMat2 :=
    ⟨⟨⟨((420058075367 : Dyadic) * half ^ 42),
        ((316813428853 : Dyadic) * half ^ 43)⟩,
       ⟨((-582497670623 : Dyadic) * half ^ 41),
        ((-551471044027 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-262922669163 : Dyadic) * half ^ 42),
        ((5680740571711 : Dyadic) * half ^ 43)⟩,
       ⟨((58308837255 : Dyadic) * half ^ 39),
        ((1539334068905 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-262922669163 : Dyadic) * half ^ 42),
        ((5680740571711 : Dyadic) * half ^ 43)⟩,
       ⟨((-58308837255 : Dyadic) * half ^ 39),
        ((-1539334068905 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-420058075367 : Dyadic) * half ^ 42),
        ((-316813428853 : Dyadic) * half ^ 43)⟩,
       ⟨((-582497670623 : Dyadic) * half ^ 41),
        ((-551471044027 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word34Step52 :
    word34Chunk52.foldl (fun acc a => a.applyPacked acc)
      word34State52 = word34State53 := by decide +kernel

private def word34Chunk53 : List Letter := [.t, .h, .s, .t, .h]
private def word34State54 : PackedMat2 :=
    ⟨⟨⟨((3884501534099 : Dyadic) * half ^ 43),
        ((868254911915 : Dyadic) * half ^ 41)⟩,
       ⟨((873379448557 : Dyadic) * half ^ 43),
        ((-617572531761 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-4175689257251 : Dyadic) * half ^ 43),
        ((1476329094965 : Dyadic) * half ^ 42)⟩,
       ⟨((938036371757 : Dyadic) * half ^ 43),
        ((-663291879469 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((4175689257251 : Dyadic) * half ^ 43),
        ((-1476329094965 : Dyadic) * half ^ 42)⟩,
       ⟨((938036371757 : Dyadic) * half ^ 43),
        ((-663291879469 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3884501534099 : Dyadic) * half ^ 43),
        ((868254911915 : Dyadic) * half ^ 41)⟩,
       ⟨((-873379448557 : Dyadic) * half ^ 43),
        ((617572531761 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word34Step53 :
    word34Chunk53.foldl (fun acc a => a.applyPacked acc)
      word34State53 = word34State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word34_check : check word34 34 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word34 = word34State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word34Chunk0 ++ word34Chunk1 ++ word34Chunk2 ++ word34Chunk3 ++
      word34Chunk4 ++ word34Chunk5 ++ word34Chunk6 ++ word34Chunk7 ++
      word34Chunk8 ++ word34Chunk9 ++ word34Chunk10 ++ word34Chunk11 ++
      word34Chunk12 ++ word34Chunk13 ++ word34Chunk14 ++ word34Chunk15 ++
      word34Chunk16 ++ word34Chunk17 ++ word34Chunk18 ++ word34Chunk19 ++
      word34Chunk20 ++ word34Chunk21 ++ word34Chunk22 ++ word34Chunk23 ++
      word34Chunk24 ++ word34Chunk25 ++ word34Chunk26 ++ word34Chunk27 ++
      word34Chunk28 ++ word34Chunk29 ++ word34Chunk30 ++ word34Chunk31 ++
      word34Chunk32 ++ word34Chunk33 ++ word34Chunk34 ++ word34Chunk35 ++
      word34Chunk36 ++ word34Chunk37 ++ word34Chunk38 ++ word34Chunk39 ++
      word34Chunk40 ++ word34Chunk41 ++ word34Chunk42 ++ word34Chunk43 ++
      word34Chunk44 ++ word34Chunk45 ++ word34Chunk46 ++ word34Chunk47 ++
      word34Chunk48 ++ word34Chunk49 ++ word34Chunk50 ++ word34Chunk51 ++
      word34Chunk52 ++ word34Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word34Step0, word34Step1, word34Step2, word34Step3, word34Step4,
      word34Step5, word34Step6, word34Step7, word34Step8, word34Step9,
      word34Step10, word34Step11, word34Step12, word34Step13, word34Step14,
      word34Step15, word34Step16, word34Step17, word34Step18, word34Step19,
      word34Step20, word34Step21, word34Step22, word34Step23, word34Step24,
      word34Step25, word34Step26, word34Step27, word34Step28, word34Step29,
      word34Step30, word34Step31, word34Step32, word34Step33, word34Step34,
      word34Step35, word34Step36, word34Step37, word34Step38, word34Step39,
      word34Step40, word34Step41, word34Step42, word34Step43, word34Step44,
      word34Step45, word34Step46, word34Step47, word34Step48, word34Step49,
      word34Step50, word34Step51, word34Step52, word34Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
