{-# OPTIONS --safe #-}

-- Tait-style rebuild prototype (Phase K). Top + Sigma fragment.
--
-- THE CORE (K.2): the semantic computability relation as a recursive
-- *function* on type structure, defined by well-founded recursion on
-- `tyDepth`. A function has no positivity obligation, so the Sigma
-- clause may quantify over `Computable` values freely.
--
-- The relations are PURE REDUCIBILITY predicates — evaluation plus the
-- recursive computability of components, with NO bundled `Derivable`
-- fields. Typing derivations are the *input* to the fundamental
-- theorem and are threaded separately; storing them here would force
-- subject expansion (false) in the backward-closure lemma.
--
-- `Acc`-irrelevance: under `--safe --without-K` two `Acc` proofs are
-- not provably `≡` (that needs funext). Instead the `*-cast` functions
-- are structural *functions* transporting a witness between any two
-- `Acc` proofs at the same `tyDepth` — funext-free.

module Tait.Computable where

open import Tait.Prelude
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
open import Induction.WellFounded using (Acc ; acc)
open import Data.Product using (Σ-syntax ; _×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

open import Tait.Syntax
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Measure

-- The family-clause depth rewrite: the second Sigma component is
-- computable at `subTy (singleSubst a) B`, whose `tyDepth` equals
-- `tyDepth B`, hence is `< tyDepth (tySigma A B)`.
subTy-snd< : (A B : RawType) (a : RawTerm)
  -> tyDepth (subTy (singleSubst a) B) < suc (tyDepth A + tyDepth B)
subTy-snd< A B a =
  subst (λ k -> k < suc (tyDepth A + tyDepth B))
        (sym (tyDepth-subTy (singleSubst a) B))
        (tyDepth-snd<Sigma A B)

-- ── Term computability ───────────────────────────────────────────
-- Pure reducibility, indexed by an accessibility proof so the
-- recursion is structural on the `Acc`.

ComputableTmAcc : (A : RawType) -> Acc _<_ (tyDepth A) -> RawTerm -> Type
ComputableTmAcc tyTop _ t = t =>e tmStar
ComputableTmAcc (tySigma A B) (acc rs) t =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ]
      (t =>e tmPair a b)
    × ComputableTmAcc A (rs (tyDepth-fst<Sigma A B)) a
    × ComputableTmAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) b

-- The user-facing relation: instantiate the canonical accessibility.
Computable : RawType -> RawTerm -> Type
Computable A t = ComputableTmAcc A (<-wf (tyDepth A)) t

-- Acc-irrelevance, as a structural function (no funext needed).
ComputableTmAcc-cast : (A : RawType) (p q : Acc _<_ (tyDepth A)) (t : RawTerm)
  -> ComputableTmAcc A p t -> ComputableTmAcc A q t
ComputableTmAcc-cast tyTop p q t x = x
ComputableTmAcc-cast (tySigma A B) (acc rsP) (acc rsQ) t
  (a , b , ev , cA , cB) =
  a , b , ev ,
  ComputableTmAcc-cast A
    (rsP (tyDepth-fst<Sigma A B)) (rsQ (tyDepth-fst<Sigma A B)) a cA ,
  ComputableTmAcc-cast (subTy (singleSubst a) B)
    (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a)) b cB

-- ── Sigma intro / elim ────────────────────────────────────────────
-- The unfolded form of `Computable (tySigma A B) t`, with the
-- components carrying the *canonical* accessibility (i.e. `Computable`,
-- not a `rs`-derived `ComputableTmAcc`). `intro`/`elim` absorb the
-- `cast` once, so downstream code never touches `Acc` directly.

SigmaComputable : RawType -> RawType -> RawTerm -> Type
SigmaComputable A B t =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ]
      (t =>e tmPair a b)
    × Computable A a
    × Computable (subTy (singleSubst a) B) b

sigmaAcc-elim : (A B : RawType) (p : Acc _<_ (tyDepth (tySigma A B))) (t : RawTerm)
  -> ComputableTmAcc (tySigma A B) p t -> SigmaComputable A B t
sigmaAcc-elim A B (acc rs) t (a , b , ev , cA , cB) =
  a , b , ev ,
  ComputableTmAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a cA ,
  ComputableTmAcc-cast (subTy (singleSubst a) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B))) b cB

sigmaAcc-intro : (A B : RawType) (p : Acc _<_ (tyDepth (tySigma A B))) (t : RawTerm)
  -> SigmaComputable A B t -> ComputableTmAcc (tySigma A B) p t
sigmaAcc-intro A B (acc rs) t (a , b , ev , cA , cB) =
  a , b , ev ,
  ComputableTmAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a cA ,
  ComputableTmAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b cB

computableSigma-elim : {A B : RawType} {t : RawTerm}
  -> Computable (tySigma A B) t -> SigmaComputable A B t
computableSigma-elim {A} {B} {t} c =
  sigmaAcc-elim A B (<-wf (tyDepth (tySigma A B))) t c

computableSigma-intro : {A B : RawType} {t : RawTerm}
  -> SigmaComputable A B t -> Computable (tySigma A B) t
computableSigma-intro {A} {B} {t} s =
  sigmaAcc-intro A B (<-wf (tyDepth (tySigma A B))) t s

-- ── Type computability ───────────────────────────────────────────
-- Types are reflexively canonical (`_=>t_` is reflexive on formers).
-- `ComputableTy` is the hereditary predicate: the components are
-- computable types, the Sigma family over already-computable args.

ComputableTyAcc : (A : RawType) -> Acc _<_ (tyDepth A) -> Type
ComputableTyAcc tyTop _ = ⊤
ComputableTyAcc (tySigma A B) (acc rs) =
    ComputableTyAcc A (rs (tyDepth-fst<Sigma A B))
  × ((a : RawTerm) -> Computable A a
       -> ComputableTyAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)))

ComputableTy : RawType -> Type
ComputableTy A = ComputableTyAcc A (<-wf (tyDepth A))

ComputableTyAcc-cast : (A : RawType) (p q : Acc _<_ (tyDepth A))
  -> ComputableTyAcc A p -> ComputableTyAcc A q
ComputableTyAcc-cast tyTop p q x = x
ComputableTyAcc-cast (tySigma A B) (acc rsP) (acc rsQ) (cA , fam) =
  ComputableTyAcc-cast A
    (rsP (tyDepth-fst<Sigma A B)) (rsQ (tyDepth-fst<Sigma A B)) cA ,
  λ a ca -> ComputableTyAcc-cast (subTy (singleSubst a) B)
    (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a)) (fam a ca)

-- ── Term-equality computability ──────────────────────────────────
-- Both sides evaluate to related canonical forms; recursion on `A`.

ComputableTmEqAcc : (A : RawType) -> Acc _<_ (tyDepth A) -> RawTerm -> RawTerm -> Type
ComputableTmEqAcc tyTop _ t u = (t =>e tmStar) × (u =>e tmStar)
ComputableTmEqAcc (tySigma A B) (acc rs) t u =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ] Σ[ c ∈ RawTerm ] Σ[ d ∈ RawTerm ]
      (t =>e tmPair a b)
    × (u =>e tmPair c d)
    × ComputableTmEqAcc A (rs (tyDepth-fst<Sigma A B)) a c
    × ComputableTmEqAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) b d

ComputableTmEq : RawType -> RawTerm -> RawTerm -> Type
ComputableTmEq A t u = ComputableTmEqAcc A (<-wf (tyDepth A)) t u

ComputableTmEqAcc-cast : (A : RawType) (p q : Acc _<_ (tyDepth A)) (t u : RawTerm)
  -> ComputableTmEqAcc A p t u -> ComputableTmEqAcc A q t u
ComputableTmEqAcc-cast tyTop p q t u x = x
ComputableTmEqAcc-cast (tySigma A B) (acc rsP) (acc rsQ) t u
  (a , b , c , d , evt , evu , cAC , cBD) =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (rsP (tyDepth-fst<Sigma A B)) (rsQ (tyDepth-fst<Sigma A B)) a c cAC ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a)) b d cBD

-- ── Type-equality computability ──────────────────────────────────
-- Recursion on both sides. Mismatched-head pairs are `⊥` — total, and
-- never built by the fundamental theorem (all closed type equalities
-- preserve the head).

ComputableTyEqAcc : (A B : RawType)
  -> Acc _<_ (tyDepth A) -> Acc _<_ (tyDepth B) -> Type
ComputableTyEqAcc tyTop tyTop _ _ = ⊤
ComputableTyEqAcc tyTop (tySigma C D) _ _ = ⊥
ComputableTyEqAcc (tySigma A B) tyTop _ _ = ⊥
ComputableTyEqAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) =
    ComputableTyEqAcc A C
      (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
  × ((a : RawTerm) -> Computable A a
       -> ComputableTyEqAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
            (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D a)))

ComputableTyEq : RawType -> RawType -> Type
ComputableTyEq A B = ComputableTyEqAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B))

ComputableTyEqAcc-cast : (A B : RawType)
    (pA qA : Acc _<_ (tyDepth A)) (pB qB : Acc _<_ (tyDepth B))
  -> ComputableTyEqAcc A B pA pB -> ComputableTyEqAcc A B qA qB
ComputableTyEqAcc-cast tyTop tyTop pA qA pB qB x = x
ComputableTyEqAcc-cast tyTop (tySigma C D) pA qA pB qB x = x
ComputableTyEqAcc-cast (tySigma A B) tyTop pA qA pB qB x = x
ComputableTyEqAcc-cast (tySigma A B) (tySigma C D)
  (acc rsABp) (acc rsABq) (acc rsCDp) (acc rsCDq) (cAC , fam) =
  ComputableTyEqAcc-cast A C
    (rsABp (tyDepth-fst<Sigma A B)) (rsABq (tyDepth-fst<Sigma A B))
    (rsCDp (tyDepth-fst<Sigma C D)) (rsCDq (tyDepth-fst<Sigma C D)) cAC ,
  λ a ca -> ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst a) D)
    (rsABp (subTy-snd< A B a)) (rsABq (subTy-snd< A B a))
    (rsCDp (subTy-snd< C D a)) (rsCDq (subTy-snd< C D a)) (fam a ca)
