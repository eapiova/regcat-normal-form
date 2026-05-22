{-# OPTIONS --safe #-}

-- Tait-style rebuild (Phase K/L). Full theory: Top, Sigma, Eq, Qtr.
--
-- THE CORE: the semantic computability relation as a recursive
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

-- ── Term/type-equality computability ─────────────────────────────
-- Term equality and type equality are mutually recursive. The Sigma
-- clauses carry the dependent-family congruence needed by later phases.

mutual
  ComputableTmEqAcc : (A : RawType) -> Acc _<_ (tyDepth A) -> RawTerm -> RawTerm -> Type
  ComputableTmEqAcc tyTop _ t u = (t =>e tmStar) × (u =>e tmStar)
  ComputableTmEqAcc (tySigma A B) (acc rs) t u =
    Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ] Σ[ c ∈ RawTerm ] Σ[ d ∈ RawTerm ]
        (t =>e tmPair a b)
      × (u =>e tmPair c d)
      × ComputableTmEqAcc A (rs (tyDepth-fst<Sigma A B)) a c
      × ComputableTmEqAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) b d
      × ComputableTyEqAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c))
  ComputableTmEqAcc (tyEq A a b) (acc rs) t u =
      (t =>e tmR) × (u =>e tmR)
    × ComputableTmEqAcc A (rs (tyDepth-base<Eq A a b)) a b
  ComputableTmEqAcc (tyQtr A) (acc rs) t u =
    Σ[ p ∈ RawTerm ] Σ[ q ∈ RawTerm ]
        (t =>e tmClass p) × (u =>e tmClass q)
      × ComputableTmEqAcc A (rs (tyDepth-base<Qtr A)) p p
      × ComputableTmEqAcc A (rs (tyDepth-base<Qtr A)) q q

  ComputableTyEqAcc : (A B : RawType)
    -> Acc _<_ (tyDepth A) -> Acc _<_ (tyDepth B) -> Type
  ComputableTyEqAcc tyTop tyTop _ _ = ⊤
  ComputableTyEqAcc tyTop (tySigma C D) _ _ = ⊥
  ComputableTyEqAcc tyTop (tyEq C c d) _ _ = ⊥
  ComputableTyEqAcc tyTop (tyQtr C) _ _ = ⊥
  ComputableTyEqAcc (tySigma A B) tyTop _ _ = ⊥
  ComputableTyEqAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) =
      ComputableTyEqAcc A C
        (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
    × ((a c : RawTerm)
         -> ComputableTmEqAcc A (rsAB (tyDepth-fst<Sigma A B)) a c
         -> ComputableTyEqAcc (subTy (singleSubst a) B) (subTy (singleSubst c) D)
              (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D c)))
  ComputableTyEqAcc (tySigma A B) (tyEq C c d) _ _ = ⊥
  ComputableTyEqAcc (tySigma A B) (tyQtr C) _ _ = ⊥
  ComputableTyEqAcc (tyEq A a b) tyTop _ _ = ⊥
  ComputableTyEqAcc (tyEq A a b) (tySigma C D) _ _ = ⊥
  ComputableTyEqAcc (tyEq A a b) (tyEq C c d) (acc rsL) (acc rsR) =
      ComputableTyEqAcc A C
        (rsL (tyDepth-base<Eq A a b)) (rsR (tyDepth-base<Eq C c d))
    × ComputableTmEqAcc A (rsL (tyDepth-base<Eq A a b)) a c
    × ComputableTmEqAcc A (rsL (tyDepth-base<Eq A a b)) b d
  ComputableTyEqAcc (tyEq A a b) (tyQtr C) _ _ = ⊥
  ComputableTyEqAcc (tyQtr A) tyTop _ _ = ⊥
  ComputableTyEqAcc (tyQtr A) (tySigma C D) _ _ = ⊥
  ComputableTyEqAcc (tyQtr A) (tyEq C c d) _ _ = ⊥
  ComputableTyEqAcc (tyQtr A) (tyQtr C) (acc rsL) (acc rsR) =
    ComputableTyEqAcc A C (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))

ComputableTmEq : RawType -> RawTerm -> RawTerm -> Type
ComputableTmEq A t u = ComputableTmEqAcc A (<-wf (tyDepth A)) t u

ComputableTyEq : RawType -> RawType -> Type
ComputableTyEq A B = ComputableTyEqAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B))

-- Acc-irrelevance for equality relations, as structural functions.

mutual
  ComputableTmEqAcc-cast : (A : RawType) (p q : Acc _<_ (tyDepth A)) (t u : RawTerm)
    -> ComputableTmEqAcc A p t u -> ComputableTmEqAcc A q t u
  ComputableTmEqAcc-cast tyTop p q t u x = x
  ComputableTmEqAcc-cast (tySigma A B) (acc rsP) (acc rsQ) t u
    (a , b , c , d , evt , evu , cAC , cBD , tyBD) =
    a , b , c , d , evt , evu ,
    ComputableTmEqAcc-cast A
      (rsP (tyDepth-fst<Sigma A B)) (rsQ (tyDepth-fst<Sigma A B)) a c cAC ,
    ComputableTmEqAcc-cast (subTy (singleSubst a) B)
      (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a)) b d cBD ,
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
      (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a))
      (rsP (subTy-snd< A B c)) (rsQ (subTy-snd< A B c)) tyBD
  ComputableTmEqAcc-cast (tyEq A a b) (acc rsP) (acc rsQ) t u (evt , evu , cab) =
    evt , evu ,
    ComputableTmEqAcc-cast A
      (rsP (tyDepth-base<Eq A a b)) (rsQ (tyDepth-base<Eq A a b)) a b cab
  ComputableTmEqAcc-cast (tyQtr A) (acc rsP) (acc rsQ) t u
    (p , q , evt , evu , cpp , cqq) =
    p , q , evt , evu ,
    ComputableTmEqAcc-cast A
      (rsP (tyDepth-base<Qtr A)) (rsQ (tyDepth-base<Qtr A)) p p cpp ,
    ComputableTmEqAcc-cast A
      (rsP (tyDepth-base<Qtr A)) (rsQ (tyDepth-base<Qtr A)) q q cqq

  ComputableTyEqAcc-cast : (A B : RawType)
      (pA qA : Acc _<_ (tyDepth A)) (pB qB : Acc _<_ (tyDepth B))
    -> ComputableTyEqAcc A B pA pB -> ComputableTyEqAcc A B qA qB
  ComputableTyEqAcc-cast tyTop tyTop pA qA pB qB x = x
  ComputableTyEqAcc-cast tyTop (tySigma C D) pA qA pB qB x = x
  ComputableTyEqAcc-cast tyTop (tyEq C c d) pA qA pB qB x = x
  ComputableTyEqAcc-cast tyTop (tyQtr C) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tySigma A B) tyTop pA qA pB qB x = x
  ComputableTyEqAcc-cast (tySigma A B) (tySigma C D)
    (acc rsABp) (acc rsABq) (acc rsCDp) (acc rsCDq) (cAC , fam) =
    ComputableTyEqAcc-cast A C
      (rsABp (tyDepth-fst<Sigma A B)) (rsABq (tyDepth-fst<Sigma A B))
      (rsCDp (tyDepth-fst<Sigma C D)) (rsCDq (tyDepth-fst<Sigma C D)) cAC ,
    λ a c eq -> ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) D)
      (rsABp (subTy-snd< A B a)) (rsABq (subTy-snd< A B a))
      (rsCDp (subTy-snd< C D c)) (rsCDq (subTy-snd< C D c))
      (fam a c
        (ComputableTmEqAcc-cast A
          (rsABq (tyDepth-fst<Sigma A B)) (rsABp (tyDepth-fst<Sigma A B)) a c eq))
  ComputableTyEqAcc-cast (tySigma A B) (tyEq C c d) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tySigma A B) (tyQtr C) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyEq A a b) tyTop pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyEq A a b) (tySigma C D) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyEq A a b) (tyEq C c d)
    (acc rsAp) (acc rsAq) (acc rsCp) (acc rsCq) (cAC , cab , cbd) =
    ComputableTyEqAcc-cast A C
      (rsAp (tyDepth-base<Eq A a b)) (rsAq (tyDepth-base<Eq A a b))
      (rsCp (tyDepth-base<Eq C c d)) (rsCq (tyDepth-base<Eq C c d)) cAC ,
    ComputableTmEqAcc-cast A
      (rsAp (tyDepth-base<Eq A a b)) (rsAq (tyDepth-base<Eq A a b)) a c cab ,
    ComputableTmEqAcc-cast A
      (rsAp (tyDepth-base<Eq A a b)) (rsAq (tyDepth-base<Eq A a b)) b d cbd
  ComputableTyEqAcc-cast (tyEq A a b) (tyQtr C) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyQtr A) tyTop pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyQtr A) (tySigma C D) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyQtr A) (tyEq C c d) pA qA pB qB x = x
  ComputableTyEqAcc-cast (tyQtr A) (tyQtr C)
    (acc rsAp) (acc rsAq) (acc rsCp) (acc rsCq) cAC =
    ComputableTyEqAcc-cast A C
      (rsAp (tyDepth-base<Qtr A)) (rsAq (tyDepth-base<Qtr A))
      (rsCp (tyDepth-base<Qtr C)) (rsCq (tyDepth-base<Qtr C)) cAC

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
ComputableTmAcc (tyEq A a b) (acc rs) t =
  (t =>e tmR) × ComputableTmEqAcc A (rs (tyDepth-base<Eq A a b)) a b
ComputableTmAcc (tyQtr A) (acc rs) t =
  Σ[ p ∈ RawTerm ] (t =>e tmClass p) × ComputableTmAcc A (rs (tyDepth-base<Qtr A)) p

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
ComputableTmAcc-cast (tyEq A a b) (acc rsP) (acc rsQ) t (ev , cEq) =
  ev ,
  ComputableTmEqAcc-cast A
    (rsP (tyDepth-base<Eq A a b)) (rsQ (tyDepth-base<Eq A a b)) a b cEq
ComputableTmAcc-cast (tyQtr A) (acc rsP) (acc rsQ) t (p , ev , cA) =
  p , ev ,
  ComputableTmAcc-cast A
    (rsP (tyDepth-base<Qtr A)) (rsQ (tyDepth-base<Qtr A)) p cA

-- ── Type computability ───────────────────────────────────────────
-- Types are reflexively canonical (`_=>t_` is reflexive on formers).
-- `ComputableTy` is the hereditary predicate: the components are
-- computable types, with Sigma families respecting term equality.

ComputableTyAcc : (A : RawType) -> Acc _<_ (tyDepth A) -> Type
ComputableTyAcc tyTop _ = ⊤
ComputableTyAcc (tySigma A B) (acc rs) =
    ComputableTyAcc A (rs (tyDepth-fst<Sigma A B))
  × ((a c : RawTerm)
       -> ComputableTmEqAcc A (rs (tyDepth-fst<Sigma A B)) a c
       -> ComputableTyEqAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
            (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c)))
ComputableTyAcc (tyEq A a b) (acc rs) =
    ComputableTyAcc A (rs (tyDepth-base<Eq A a b))
  × Computable A a
  × Computable A b
ComputableTyAcc (tyQtr A) (acc rs) =
  ComputableTyAcc A (rs (tyDepth-base<Qtr A))

ComputableTy : RawType -> Type
ComputableTy A = ComputableTyAcc A (<-wf (tyDepth A))

ComputableTyAcc-cast : (A : RawType) (p q : Acc _<_ (tyDepth A))
  -> ComputableTyAcc A p -> ComputableTyAcc A q
ComputableTyAcc-cast tyTop p q x = x
ComputableTyAcc-cast (tySigma A B) (acc rsP) (acc rsQ) (cA , fam) =
  ComputableTyAcc-cast A
    (rsP (tyDepth-fst<Sigma A B)) (rsQ (tyDepth-fst<Sigma A B)) cA ,
  λ a c eq -> ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (rsP (subTy-snd< A B a)) (rsQ (subTy-snd< A B a))
    (rsP (subTy-snd< A B c)) (rsQ (subTy-snd< A B c))
    (fam a c
      (ComputableTmEqAcc-cast A
        (rsQ (tyDepth-fst<Sigma A B)) (rsP (tyDepth-fst<Sigma A B)) a c eq))
ComputableTyAcc-cast (tyEq A a b) (acc rsP) (acc rsQ) (cA , ca , cb) =
  ComputableTyAcc-cast A
    (rsP (tyDepth-base<Eq A a b)) (rsQ (tyDepth-base<Eq A a b)) cA ,
  ca ,
  cb
ComputableTyAcc-cast (tyQtr A) (acc rsP) (acc rsQ) cA =
  ComputableTyAcc-cast A
    (rsP (tyDepth-base<Qtr A)) (rsQ (tyDepth-base<Qtr A)) cA

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

-- ── Qtr intro / elim ──────────────────────────────────────────────

QtrComputable : RawType -> RawTerm -> Type
QtrComputable A t =
  Σ[ p ∈ RawTerm ] (t =>e tmClass p) × Computable A p

qtrAcc-elim : (A : RawType) (p : Acc _<_ (tyDepth (tyQtr A))) (t : RawTerm)
  -> ComputableTmAcc (tyQtr A) p t -> QtrComputable A t
qtrAcc-elim A (acc rs) t (p , ev , cA) =
  p , ev ,
  ComputableTmAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) p cA

qtrAcc-intro : (A : RawType) (p : Acc _<_ (tyDepth (tyQtr A))) (t : RawTerm)
  -> QtrComputable A t -> ComputableTmAcc (tyQtr A) p t
qtrAcc-intro A (acc rs) t (p , ev , cA) =
  p , ev ,
  ComputableTmAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) p cA

computableQtr-elim : {A : RawType} {t : RawTerm}
  -> Computable (tyQtr A) t -> QtrComputable A t
computableQtr-elim {A} {t} c =
  qtrAcc-elim A (<-wf (tyDepth (tyQtr A))) t c

computableQtr-intro : {A : RawType} {t : RawTerm}
  -> QtrComputable A t -> Computable (tyQtr A) t
computableQtr-intro {A} {t} q =
  qtrAcc-intro A (<-wf (tyDepth (tyQtr A))) t q

-- ── Eq intro / elim ───────────────────────────────────────────────

eqAcc-elim : (A : RawType) (a b : RawTerm) (p : Acc _<_ (tyDepth (tyEq A a b))) (t : RawTerm)
  -> ComputableTmAcc (tyEq A a b) p t -> (t =>e tmR) × ComputableTmEq A a b
eqAcc-elim A a b (acc rs) t (ev , cEq) =
  ev ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Eq A a b)) (<-wf (tyDepth A)) a b cEq

eqAcc-intro : (A : RawType) (a b : RawTerm) (p : Acc _<_ (tyDepth (tyEq A a b))) (t : RawTerm)
  -> (t =>e tmR) × ComputableTmEq A a b -> ComputableTmAcc (tyEq A a b) p t
eqAcc-intro A a b (acc rs) t (ev , cEq) =
  ev ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Eq A a b)) a b cEq

computableEq-elim : {A : RawType} {a b t : RawTerm}
  -> Computable (tyEq A a b) t -> (t =>e tmR) × ComputableTmEq A a b
computableEq-elim {A} {a} {b} {t} c =
  eqAcc-elim A a b (<-wf (tyDepth (tyEq A a b))) t c

computableEq-intro : {A : RawType} {a b t : RawTerm}
  -> (t =>e tmR) × ComputableTmEq A a b -> Computable (tyEq A a b) t
computableEq-intro {A} {a} {b} {t} c =
  eqAcc-intro A a b (<-wf (tyDepth (tyEq A a b))) t c
