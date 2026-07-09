# SurfaceEffects

SurfaceEffects is a Rocq mechanization of a language with regions, heap
effects, dynamic traces, parallel pairs, and effect soundness.

## Current Build

Known local toolchain:

```sh
opam switch surfaceeffects
eval $(opam env)
rocq -v
make
```

The current workspace builds with:

```text
The Rocq Prover, version 9.1.1
compiled with OCaml 4.14.2
```

Both `rocq` and `coqc` report this Rocq version in the current switch.

Expected build result:

```sh
make
```

The full project currently compiles. There are no source-level `Axiom` or
`Admitted` declarations in `theories/`.

Rocq 9 emits some compatibility warnings:

- `From Coq` imports are deprecated in favor of `From Stdlib`.
- A few notation declarations have incompatible prefixes.

These warnings do not currently block the build.

## Current Source Layout

The source tree is organized by dependency layer:

```text
theories/
  Core/
    Regions.v
    Expressions.v
    Values.v
    ComputedActions.v
    DynamicActions.v
    StaticActions.v

  Runtime/
    Heap.v
    TraceSemantics.v
    HeapTyping.v
    Semantics.v

  Typing/
    TypeSyntax.v
    TypingJudgments.v

  Meta/
    Tactics.v
    LocallyNameless.v
    MapFacts.v
    RegionSubstitutionFacts.v
    RegionFacts.v
    TypeSubstitutionFacts.v
    EffectFreeVarsFacts.v
    EffectFacts.v
    TypingWeakeningFacts.v
    TypeFacts.v
    StoreFacts.v
    TraceFacts.v
    HeapFacts.v
    TraceTypingFacts.v

  Soundness/
    TypeSystem.v
    EffectSystem.v
    Correctness.v

  Determinism/
    ReadOnlyDeterminism.v
    Determinism.v
    DeterminismExt.v
```

`Definitions/Axioms.v` is no longer part of the source tree or `_CoqProject`.
The old `Definitions/` and `Proofs/` directories may still contain generated
build artifacts after local compilation, but they no longer contain source files
listed by `_CoqProject`.

## Proof Status

The main type soundness theorem is now stratified internally:

- `ty_sound_strong` proves type soundness together with a trace typing
  invariant.
- `ty_sound` preserves the older public interface by projecting away that
  extra invariant.
- `TcHeap_Extended_2` is proved without an admission.
- The `BS_Set_Ref` semantics includes the side condition that assignment only
  writes to an existing location after evaluating the assigned value.
- Concrete read/write and write/write computed-action disjointness is based on
  concrete address inequality `(region, location) <> (region, location)`, so
  same-region accesses to distinct locations can be accepted by the parallel
  disjointness check.

The trace typing invariant records that dynamic allocation and write actions
are justified by the final store typing. This is what makes the parallel heap
extension proof go through without an axiom.

## Remaining Stratification Work

The source files have been moved into strata. The former `GTypes.v` content has
been split into type syntax and typing judgments, and the former `GHeap.v`
content has been split into heap operations, trace semantics, and heap typing.
Trace replay and read-only trace/evaluation lemmas have been moved from
`HeapFacts.v` into `TraceFacts.v`, and downstream files now import the trace
facts explicitly when they need them. The old compatibility wrappers have also
been removed from `_CoqProject`. Store-extension facts now live in
`StoreFacts.v`, and the trace typing invariant plus its heap-replay lemmas live
in `TraceTypingFacts.v`. Generic finite-map lookup/update lemmas live in
`MapFacts.v`, store-weakening facts live in `TypingWeakeningFacts.v`, and
low-level region substitution/fold lemmas live in `RegionSubstitutionFacts.v`.
`RegionFacts.v` now keeps the higher-level `TcRho` no-free-vars theorem family.
Type-level substitution commutation and rho-extension fold lemmas live in
`TypeSubstitutionFacts.v`, while `TypeFacts.v` keeps typing closure and
environment-extension facts. Effect free-variable/inclusion support lives in
`EffectFreeVarsFacts.v`, leaving `EffectFacts.v` focused on effect unions,
conflict/disjointness facts, soundness, and read-only preservation. The next
cleanup is to make the remaining large fact files match the strata more
precisely. Dependencies should continue to flow in one direction. In
particular, core/read-only determinism supports soundness, while extended
determinism sits after correctness:

```text
Core < Runtime < Typing < Meta < Core Determinism < Soundness < Extended Determinism
```

A more refined target after splitting large files:

```text
theories/
  Core/
    Names.v              # identifiers, regions, shared finite-map utilities
    Syntax.v             # expressions and values
    StaticActions.v      # static actions and static effects
    DynamicActions.v     # dynamic actions and traces
    ComputedActions.v    # computed effects

  Runtime/
    Heap.v               # heaps and heap operations
    Semantics.v          # big-step semantics
    TraceSemantics.v     # trace replay relation and trace execution facts

  Typing/
    Types.v              # Tau, Gamma, Sigma, Omega
    Contexts.v           # typing contexts, store typings, environments
    ExprTyping.v         # TcExp, TcVal, TcEnv, TcRho, TcInc
    EffectTyping.v       # static/dynamic effect typing judgments

  Meta/
    Tactics.v
    LocallyNameless.v
    MapFacts.v
    RegionSubstitutionFacts.v
    RegionFacts.v
    TypeSubstitutionFacts.v
    EffectFreeVarsFacts.v
    TypingWeakeningFacts.v
    StoreFacts.v
    HeapFacts.v
    TraceFacts.v
    TraceTypingFacts.v
    TypeFacts.v
    EffectFacts.v

  Soundness/
    TypeSoundness.v
    EffectSoundness.v
    Correctness.v

  Determinism/
    CoreDeterminism.v
    ReadOnlyDeterminism.v
    ExtendedDeterminism.v
```

Suggested next migration order:

1. Split the remaining large fact files by subject: region facts, type facts,
   effect facts, and any residual heap/trace facts.
2. Trim direct imports after each split so files mention only the layer they use.
3. Rename theorem files once the contents are stable: `TypeSystem.v` to
   `TypeSoundness.v`, `EffectSystem.v` to `EffectSoundness.v`, and
   `DeterminismExt.v` to `ExtendedDeterminism.v`.

The important rule is that lower layers should never import higher layers. For
example, `Runtime/Semantics.v` should not import typing proofs, and `Meta/`
facts should not import final soundness theorems.
