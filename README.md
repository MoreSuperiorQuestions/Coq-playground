# Coq playground

My practice project for Coq, OCaml, and git.

## TAPL Chapter 6: de Bruijn indices

[`DeBruijn.v`](DeBruijn.v) is a deliberately small, TAPL-style development of
nameless lambda terms. It contains:

- syntax where `var x n` records both de Bruijn index `x` and context length `n`;
- cutoff-based upward shifting;
- substitution and top-level substitution;
- an explicit downward shift, kept separate so its precondition is visible;
- a scoping invariant that checks both the index and stored context length;
- small executable examples and foundational lemmas.

The intended reading order is the order in the file. In VS Code, step through
one command at a time and watch the context and goal after each tactic.

### The central invariant

`well_scoped n t` means that `t` may be used in a context of length `n`.
At every variable `var x stored_n`, it checks:

```text
stored_n = n    and    x < n
```

This explains why TAPL stores the otherwise redundant second number: a shift
that updates the index but forgets the context length violates the invariant.

### Three operations to compare

```coq
shift d c t
subst j s t
subst_top s t
```

- `shift d c t` adds `d` to indices at or above cutoff `c`; entering an
  abstraction raises the cutoff.
- `subst j s t` replaces index `j`; entering an abstraction raises `j`.
- `subst_top s t` implements TAPL's `termSubstTop`: first lift `s`, perform
  substitution at index `0`, then remove the discharged binder.

### Suggested study checkpoints

1. Compute `shift 1 0 id` by hand, including every stored context length.
2. Explain why the abstraction case of `shift` uses cutoff `S c`.
3. Step through `subst_under_binder` and locate the initial upward shift and
   the final downward shift.
4. Temporarily stop updating `n` in `shift`; identify exactly where
   `shift_preserves_scoping` fails.

### Build

With Rocq/Coq available on macOS:

```sh
make
```

Or compile the file directly:

```sh
coqc DeBruijn.v
```

The development uses only the standard library modules `Arith` and `Lia`.

### Natural next steps

Keep the project small and add one concept at a time:

1. prove the corresponding scoping theorem for `subst`;
2. replace total `shift_down` with a checked operation returning `option tm`;
3. define one-step call-by-value evaluation and prove determinism.
