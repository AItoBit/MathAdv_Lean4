# MathAdv_Lean4

**Lean 4 formalizations of proofs for the [MathAdv](https://github.com/margotyjx/MathAdv) exercises.**

This repository collects machine-checkable Lean 4 proofs for the advanced‑mathematics
problems in the MathAdv benchmark ("What Theorem Provers Know, Reason, Formalize, and
Generalize"). Each file takes one exercise, states it as a Lean theorem, and proves it
against [Mathlib](https://github.com/leanprover-community/mathlib4).

## Contents

- ~150 standalone Lean files, `MathAdv_0.lean` … `MathAdv_150.lean`
  (a handful of numbers are not present; `MathAdv_45.lea` is an extension typo for `.lean`).
- `LICENSE` — MIT.

Every file is self‑contained:

- It begins with `import Mathlib`.
- It carries a doc comment (`/-- … -/` or `/-! … -/`) restating the problem in prose.
- The theorem is named after the source it comes from (e.g. `Gallian_1`, `Gallian_2`,
  `strang_13_5_11`), not after the file number.
- Some of the heavier analysis files raise elaboration limits and set pretty‑printer /
  `autoImplicit` options at the top, e.g.:

  ```lean
  set_option maxHeartbeats 8000000
  set_option maxRecDepth 4000
  set_option autoImplicit false
  ```

### Topics covered

The exercises range across the undergraduate/early‑graduate curriculum, for example:

| Area | Example |
| --- | --- |
| Group theory (Gallian) | order of powers in a cyclic group; `⟨a^k⟩ = ⟨a^{gcd(n,k)}⟩` via Bézout |
| Complex analysis (Strang) | holomorphic functions satisfy Laplace's equation, with a counterexample to a naïve reading |
| Real analysis | Weierstrass approximation theorem (via Fejér) |

Some files also include deliberately "literal but false" variants of a statement
(e.g. `strang_13_5_11_literal_false`) with an explicit counterexample, mirroring the
junk‑theorem study in the upstream benchmark.

## Requirements

- [Lean 4](https://leanprover.github.io/) with [`elan`](https://github.com/leanprover/elan)
- A Mathlib build matching your Lean toolchain

> Note: this repo is currently a flat set of `.lean` files with no `lakefile` /
> `lean-toolchain` checked in. To check the proofs, drop the files into a Lake project
> that depends on Mathlib (see below).

## Checking a proof

Create a Lake project with Mathlib as a dependency:

```bash
lake new mathadv_check math
cd mathadv_check
# add mathlib to lakefile, then:
lake update
lake exe cache get
```

Copy any `MathAdv_*.lean` file into the project (fixing `MathAdv_45.lea` → `.lean`),
add it to your root module or reference it directly, and build:

```bash
lake build
```

A file that builds with no `sorry` and no errors is a complete, verified proof.

## Relationship to upstream

The problem statements and numbering come from
[margotyjx/MathAdv](https://github.com/margotyjx/MathAdv). This repository contributes
only the Lean 4 formalizations and their proofs.

## License

MIT — see [`LICENSE`](LICENSE).
