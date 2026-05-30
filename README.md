# Modular Normal Forms for Categorical Type Theories

A machine-checked **Agda** formalisation of the *canonical normal form
theorem* for the type theory of regular categories.

The theorem says that every derivable judgement of the type theory
`T_reg` has a canonical normal form: every closed term evaluates to an
introductory (canonical) form of its type. Its consequences include
the introductory-form property, canonicity, and consistency of the
calculus.

`T_reg` is the internal language of regular categories in Maietti's
modular correspondence between extensions of dependent type theory and
classes of categories. This repository focuses on the regular-category
level of that hierarchy. It has four judgement forms — type, type
equality, term, term equality — and the type formers `⊤`, `Σ`,
extensional propositional equality `Eq`, and effective quotients `Qtr`.

## Two developments

This repository contains **two** formalisations of the same theorem.
Together they tell the story of the proof's *formalisation
architecture* — itself a contribution of this work.

### `src/Tait/` — the complete result

A Tait-style logical-relations proof. The computability predicate is a
recursive **function on type structure**; the fundamental theorem
recurses on syntactic size. This development is:

- **16 modules, every one `{-# OPTIONS --safe #-}`**;
- **zero `{-# TERMINATING #-}` pragmas, zero `postulate`, zero holes**;
- the headline theorem `canonicalFormTheorem : Derivable J →
  CanonicalForm J` is machine-checked for all four type formers;
- non-vacuity is `refl`-verified in `src/Tait/Smoke.agda` — the
  theorem genuinely normalises concrete `Σ`-, `Eq`- and
  quotient-eliminators to their canonical forms.

### `src/TReg/` — the direct attempt

An earlier formalisation in which `Computable` is an inductive data
type and "substitution preserves computability" is proven by recursion
on derivations with a syntactic `derivSize` measure. This approach
runs into the standard logical-relations / reducibility circularity:
no fixed lexicographic measure satisfies both the `Σ`-family
substitution edge and the `Σ`-elimination edge. It type-checks with
**two** narrow `{-# TERMINATING #-}` pragmas in
`src/TReg/CompTheorem.agda` (18 of its 21 modules are `--safe`).

`src/Tait/` is the resolution of what `src/TReg/` left open: rebuilding
the semantic relation so it recurses on type structure dissolves the
cycle, and the proof becomes genuinely, fully `--safe`.

## Toolchain

- [Agda](https://github.com/agda/agda) 2.9
- [agda-stdlib](https://github.com/agda/agda-stdlib) 2.3, registered
  as the library `standard-library-2.3`

## Building

```sh
# the complete, fully --safe development:
agda --safe src/Tait/Everything.agda

# the earlier direct attempt (2 TERMINATING pragmas, not fully --safe):
agda src/TReg/Everything.agda
```

`src/Tait/Everything.agda` checks from a cold build in seconds.

## Relation to the thesis

The theorem and its proof are from R. Borsetto's MSc thesis at the
University of Padova, which also gave a *partial* formalisation in Coq.
That Coq development lives at
[`eapiova/canonical-normal-form-regular-categories`](https://github.com/eapiova/canonical-normal-form-regular-categories).
The present repository is the complete Agda re-formalisation, covering
the whole type theory of regular categories.

An abstract on this work was accepted at SSTT 2026.
