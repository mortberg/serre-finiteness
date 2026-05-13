{-

This is a summary file to accompany the paper

A computer formalisation of the Serre finiteness theorem
Reid Barton, Axel Ljungström, Owen Milner, Anders Mörtberg

Checked against the agda/cubical library (commit d0b9c7b0e9e4f816422c3447d7983b03274dd829, Wed May 13 2026)

-}

{-# OPTIONS --safe #-}

module Summary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.EilenbergMacLane.Base

open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

open import Cubical.CW.Base
open import Cubical.CW.Instances.Pushout

variable
    ℓ : Level

open import SerreFinitenessTheorem

open import SAF

open import PointedHITs

open import HomotopyGroups

open import FPAbGroup

open import FiniteCW

open import CorollariesToHurewicz

open import CorollariesToGanea

open import Connectedness

open import LastMinuteLemmas.AlgebraLemmas
open import LastMinuteLemmas.ConnectedLemmas
open import LastMinuteLemmas.CWLemmas
open import LastMinuteLemmas.CWResize
open import LastMinuteLemmas.EM
open import LastMinuteLemmas.FinLemmas
open import LastMinuteLemmas.SmashLemmas
open import LastMinuteLemmas.Smith
open import LastMinuteLemmas.SuspLemmas

open import FiberOrCofiberSequences.Base
open import FiberOrCofiberSequences.ChainOfFibers
open import FiberOrCofiberSequences.CofiberBase
open import FiberOrCofiberSequences.LongExactSequence
open import FiberOrCofiberSequences.PuppeLemma
open import FiberOrCofiberSequences.ShortExact
open import FiberOrCofiberSequences.ShortExactSequence

open import ConnectedCovers.Base
open import ConnectedCovers.EMIsFiber
open import ConnectedCovers.EquivPreservation
open import ConnectedCovers.GeneralisingFreudnthl
open import ConnectedCovers.K-G-n-facts
open import ConnectedCovers.PointedEquivalences
open import ConnectedCovers.TruncationLevelFacts
open import ConnectedCovers.UsefulLemmas

------ Section 2: Background ------

-- Initial connectedness propositions are from the cubical library and
-- not formalised by us, so we omit them.

-- Definition 5 (Fibre Sequences)
Definition-5 : (X Y Z : Pointed₀) → Type₁
Definition-5 = FiberSeq

-- Long exact sequence of homotopy groups
-- Where (fiberSequence F) is the sequence of groups:
-- ..., π (n + 1) (Z), π n X, π n Y, π n Z, π (n - 1) X, ...
-- and (fiberSequenceEdges F) is the sequence of maps between them,
-- this is a proof that together these form a long exact sequence of groups.
Long-exact-sequence : {X Y Z : Pointed ℓ} (F : FiberSeq X Y Z) → isLES (fiberSequence F) (fiberSequenceEdges F)
Long-exact-sequence F = fiberSequenceIsLES F

-- Definition 6 (Cofibre Sequences)
Definition-6 : (X Y Z : Pointed₀) → Type₁
Definition-6 = CofiberSeq

-- Proposition 7 (if X → Y → Z is a cofibre sequence, then so is Y → Z → Susp X)
Proposition-7 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → CofiberSeq Y Z (S∙ X)
Proposition-7 X Y Z = copuppe

-- Corollary 8
-- Susp n X → Susp n Y → Susp n Z is a cofiber sequence
Corollary-8-1 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ n X) (Susp∙^ n Y) (Susp∙^ n Z)
Corollary-8-1 X Y Z S n = copuppe-Cof n S
-- Susp n Y → Susp n Z → Susp (1 + n) X is a cofiber sequence
Corollary-8-2 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ n Y) (Susp∙^ n Z) (Susp∙^ (suc n) X)
Corollary-8-2 X Y Z S n = copuppe-Dom n S
-- Susp n Z → Susp (1 + n) X → Susp (1 + n) Y is a cofiber sequence
Corollary-8-3 : (X Y Z : Pointed₀) → CofiberSeq X Y Z → (n : ℕ) → CofiberSeq (Susp∙^ n Z) (Susp∙^ (suc n) X) (Susp∙^ (suc n) Y)
Corollary-8-3 X Y Z S n = copuppe-Ext n S

-- Proposition 9 (connectivity of maps between cofibers)
Proposition-9 : (n : ℕ) {X Y Z X' Y' Z' : Pointed ℓ}
    (S : CofiberSeq X Y Z) (S' : CofiberSeq X' Y' Z')
    (f : X →∙ X') (g : Y →∙ Y')
    (p : (g ∘∙ CofiberSeqInc S) ≡ (CofiberSeqInc S' ∘∙ f))
    → isConnectedFun n (fst f)
    → isConnectedFun (1 + n) (fst g)
    → isConnectedFun (1 + n) (fst (CofiberSeqMap S S' f g p))
Proposition-9 = CofiberSeqMapConn

-- Corollary 10 (connectivity of suspension map)
Corollary-10 : (n : ℕ) {X Y : Type₀} (f : X → Y)
  → isConnectedFun n f
  → isConnectedFun (suc n) (suspFun f)
Corollary-10 n f cf = isConnectedSuspFun f n cf

-- Proposition 11 (connectivity of join map)
Proposition-11 : {ℓ' : Level} {X₁ X₂ : Type ℓ} {Y₁ Y₂ : Type ℓ'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    (n₁ n₂ m₁ m₂ : HLevel)
    (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
    → isConnectedFun n₁ f₁ → isConnectedFun n₂ f₂
    → isConnected m₁ X₁ → isConnected m₂ Y₂
    → isConnectedFun k (join→ f₁ f₂)
Proposition-11 = isConnectedFunJoin


------ Section 3: A rough outline of the formalised proof ------

-- Definition 12 (Connected Covers)
Definition-12 : Pointed₀ → ℕ → Pointed₀
Definition-12 = _<_>

-- Master theorem A (SAF is closed under taking connected covers)
Theorem-A : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → saf (X < (suc n) >)
Theorem-A = saf→saf<->

-- Master theorem B (lowest non-trivial homotopy group of a highly connected SAF space is FP)
Theorem-B : (X : Pointed ℓ) (hX : saf X) (n : ℕ) (cX : isConnected (3 + n) (typ X)) → isFP (πAb n X)
Theorem-B = saf→isFPBottomπ

-- Note: there is a minor typo in the paper for Theorem 13 ∙ the type
-- X should be 1-connected.
Theorem-13 : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ) → isFP (πAb n X)
Theorem-13 = saf→isFPπ

-- Theorem 14 is expository only and not part of the formalisation


-- Definition 16 (Finite CW Complexes)
-- Universe polymorphic
Definition-16 : (ℓ : Level) → Type (ℓ-suc ℓ)
Definition-16 = FinCW

-- Example 17 (FinCW is closed under Susp)
Example-17 : (n : ℕ) (C : Type ℓ) → isFinCW C → isFinCW (Susp^ n C)
Example-17 {ℓ} n C = isFinCWSusp {ℓ} {n} C


-- Definition 18 (n-Finite Types)
-- Note that the Agda conventions for finiteness of types and dimensions of CW complexes are off by one from what appears in the paper
-- To translate from Agda indices to paper indices, subtract one.
Definition-18 : HLevel → Type ℓ → Type (ℓ-suc ℓ)
Definition-18 = nFinite-nDim

-- Proposition 19 (transferring finiteness along connected maps)
-- Note also that conventions for connectedness are off by two
-- So here, in the numbering conventions of the paper, our hypotheses are that Y is (n - 1)-finite, and f is (n - 1)-connected
Proposition-19 : {X Y : Type ℓ} (f : X → Y)
                 (n : HLevel) (hf : isConnectedFun (1 + n) f)
                 → nFinite n Y → nFinite n X
Proposition-19 = nFiniteApprox'

-- Propossition 20 (nFinite types are closed under taking cofibers)
Proposition-20 : {n : ℕ} {X Y Z : Pointed ℓ} → CofiberSeq X Y Z
    → nFinite n (typ X)
    → nFinite (1 + n) (typ Y)
    → nFinite (1 + n) (typ Z)
Proposition-20 = cofNFinite


-- Proposition 21 (product of n-finite types are n-finite) is omitted
-- as the statement is never used explicitly in the formalisation
-- (rather, it appears inlined in the proof of the corresponding
-- property for stably almost finite types)

-- Definition 22 (Stably n-Finite Types)
Definition-22 : HLevel → Pointed ℓ → Type (ℓ-suc ℓ)
Definition-22 = stablyNFinite

-- Propositions 23 and 24 (join is stably k-finite for suitable k)
Proposition-23 : (X Y : Pointed ℓ) (m₁ m₂ n₂ : HLevel)
  (hXm₁ : isConnected (m₁ + 2) (typ X)) (hX₁ : stablyNFinite 1 X)
  (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ 1 + m₂) (hk₂ : k ≤ n₂ + (m₁ + 2))
  → stablyNFinite k (join∙ X Y)
Proposition-23 {ℓ} X Y = stablyNFiniteJoin-alt {ℓ} {X} {Y}

Proposition-24 : (X Y : Pointed ℓ) (m₁ n₁ m₂ n₂ : HLevel)
  (hmn₁ : m₁ ≤ n₁)
  (hXm₁ : isConnected m₁ (typ X)) (hXn₁ : stablyNFinite n₁ X)
    (hXm₂ : isConnected m₂ (typ Y)) (hXn₂ : stablyNFinite n₂ Y)
  (k : HLevel) (hk₁ : k ≤ n₁ + m₂) (hk₂ : k ≤ n₂ + m₁)
  → stablyNFinite k (join∙ X Y)
Proposition-24 {ℓ} X Y = stablyNFiniteJoin {ℓ} {X} {Y}


-- Definition 25 (Stably Almost Finite Types)
Definition-25 : Pointed ℓ → Type (ℓ-suc ℓ)
Definition-25 = saf

-- Proposition 26 (more closure properties for stably almost finite types)
-- Closure under products
Proposition-26-1 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ×∙ Y)
Proposition-26-1 {ℓ} {X} {Y} = saf× {ℓ} {X} {Y}
-- Closure under V (wedge product)
Proposition-26-2 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋁∙ₗ Y)
Proposition-26-2 {ℓ} {X} {Y} = saf⋁ {ℓ} {X} {Y}
-- Closure under /\ (smash product)
Proposition-26-3 : {X Y : Pointed ℓ} → saf X → saf Y → saf (X ⋀∙ Y)
Proposition-26-3 = saf⋀

-- Note that the file SAF.agda contains proofs of many more closure properties for all these concepts, we have only highlighted a few in the paper.

-- Corollary 28 combined with Theorem 27 (iterating Ganea)
module Corollary-28 {F : Pointed ℓ} {B : Pointed ℓ} (j : F →∙ B) where
    open Ganea^ j
    -- The ``elbow'' cofibre sequences, for instance
    -- fiber * ...
    --  |
    --  V
    --  E^(n) --> E^(n + 1)
    -- notice we are using the variable E where the paper uses C
    ElbowCofibreSeq : (n : ℕ) → CofiberSeq (join-F n) (E n) (E (1 + n))
    ElbowCofibreSeq = GaneaCofiberSeq

-- Proposition 29 (if B is connected and (Ω B) is SAF, so is B)
-- Remember connectedness conventions are off-by-two
Proposition-29 : {B : Pointed ℓ} (cB : isConnected 2 (typ B)) → saf (Ω B) → saf B
Proposition-29 = safΩ→saf

-- Proposition 30 (if B is 1-connected and SAF, then so is (Ω B))
Proposition-30 : {B : Pointed ℓ} (scB : isConnected 3 (typ B)) → saf B → saf (Ω B)
Proposition-30 = saf→safΩ

-- Proposition 31 (if F → E → B is a fibre sequence and B is 1-connected, and B and F are SAF, then so is E)
Proposition-31 : {F E B : Pointed ℓ} (S : FiberSeq F E B) (scB : isConnected 3 (typ B)) → saf B → saf F → saf E
Proposition-31 = safTotal

-- Proposition 32 (same as above, but for fibres) ... this lemma is
-- meant to be expository and is never actually used explicitly in the
-- formalisation , so we omit it. However, we remark that there is a
-- small typo in the paper: like in Proposition 31, B has to be
-- 1-connected.

-- Proposition 33 (Eilenberg-MacLane spaces) ... Already in the library
Proposition-33 = EM∙

-- Proposition 34 (fiber of the map X<n + 1> → X<n> is an Eilenberg-MacLane space)
-- Indices shifted-by-one
Proposition-34 : (X : Pointed ℓ) (n : ℕ) → FiberSeq (EM∙ (πAb n X) (suc n)) (X < (2 + n) >) (X < (suc n) >)
Proposition-34 = <->EMFibSeq

-- Proposition 35 (if G is FP, then K(G, n) are all SAF)
Proposition-35 : (G : AbGroup ℓ) (fpG : isFP G) (n : ℕ) → saf (EM∙ G (suc n))
Proposition-35 = isFP→safEM'

-- Lemma 36: expository only and omitted from formalisation

-- Theorem 37 (Weak Hurewicz theorem): never included explicitly but
-- appears in the where clause in proof of saf→isFPBottomπ (Master
-- theorem B)

-- The remaining theorems up until the Serre Finiteness Theorem are
-- omitted since they are not part of this formalisation.

-- Theorem 40 (The Serre Finiteness Theorem)
-- Note that we introduce some special notation -- πSphere n m -- for the nth homotopy groups of the m-dimensional sphere
Theorem-40 : (n m : ℕ) → isFP (πSphere n m)
Theorem-40 = isFPπSphere

------ Section 4: On the formalisation ------

-- Proposition 41 (Induction for finitely presentable abelian groups)
Proposition-41 : (P : AbGroup₀ → Type ℓ) → (∀ G → isProp (P G))
   → (∀ n → P (ℤMod n))
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ G → isFP G → (P G))
Proposition-41 = indFP

-- Proposition 42 (Induction for CW complexes) ∙ Merged with the library already
Proposition-42 : ∀ {ℓ ℓ'} (P : Type ℓ → Type ℓ')
  (P-unit : P Unit*)
  (P-empty : P ⊥*)
  (P-pushout : (A B C : Type ℓ) (f : A → B) (g : A → C) →
               P A → P B → P C → P (Pushout f g))
  (B : finCW ℓ) → isProp (P (fst B)) → P (fst B)
Proposition-42 = elimPropFinCW
