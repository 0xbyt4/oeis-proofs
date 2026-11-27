# oeis-proofs

Proofs and Lean 4 formalizations of statements that the On-Line Encyclopedia
of Integer Sequences (OEIS) records as conjectures.

Many OEIS entries carry statements marked "Conjecture", "Apparently" or
"Empirical". This repository collects proofs of such statements. Each result
has a written proof, a numerical check and a Lean 4 formalization.

The results are small. Most of them follow from classical theorems by a short
argument, and each proof file says so in its "Prior work" section. The
purpose of the repository is to settle the conjecture labels with complete,
machine-checked proofs. It does not claim new methods.

## Method

For every statement we do these steps:

1. Check that the OEIS entry still lists the statement as unproved.
2. Search the literature for an existing proof and for the classical results
   that the statement depends on. Record the findings in the proof file.
3. Test the statement numerically with a dependency-free Python script.
4. Write a complete human-readable proof with references.
5. Formalize the proof in Lean 4 with Mathlib.
6. Record which statements the Lean file proves and which it does not.

## Layout

| Path | Content |
| --- | --- |
| `proofs/` | One Markdown file per result, with statement, proof and remarks |
| `verify/` | Numerical checks, Python 3 standard library only |
| `OeisProofs/` | Lean 4 formalizations, one file per result |
| `OeisProofs.lean` | Root module that imports every formalization |

## Results

| OEIS entry | Statement | Proof | Numerical check | Lean |
| --- | --- | --- | --- | --- |
| [A306598](https://oeis.org/A306598) | The circulant determinant of the divisors of n is positive for squares and negative otherwise | [proof](proofs/A306598.md) | [script](verify/a306598.py) | [file](OeisProofs/A306598.lean) |
| [A343752](https://oeis.org/A343752) | a(n) = n if and only if n is a triangular number | [proof](proofs/A343752.md) | [script](verify/a343752.py) | [file](OeisProofs/A343752.lean) |
| [A372966](https://oeis.org/A372966) | sigma_8(n^2)/sigma_4(n^2) is congruent to 1 modulo 240, and 240 is optimal | [proof](proofs/A372966.md) | [script](verify/a372966.py) | [file](OeisProofs/A372966.lean) |
| [A365849](https://oeis.org/A365849) | Every term after the first is congruent to 1 modulo 36 | [proof](proofs/A365849.md) | [script](verify/a365849.py) | [file](OeisProofs/A365849.lean) |
| [A352446](https://oeis.org/A352446), [A341309](https://oeis.org/A341309), [A352269](https://oeis.org/A352269) | Generating function, divisor description and row sums for the number of parts in partitions into consecutive parts | [proof](proofs/A352446.md) | [script](verify/a352446.py) | [file](OeisProofs/A352446.lean) |
| [A292042](https://oeis.org/A292042), [A292043](https://oeis.org/A292043) | Series formulas for the real and imaginary parts of (ix; x)_infinity | [proof](proofs/A292042.md) | [script](verify/a292042.py) | [file](OeisProofs/A292042.lean) |
| [A389343](https://oeis.org/A389343), [A390208](https://oeis.org/A390208), [A390217](https://oeis.org/A390217), [A387957](https://oeis.org/A387957), [A392002](https://oeis.org/A392002) | Generating functions for colored partitions with color sum in a residue class modulo m, for every m | [proof](proofs/colored-partitions.md) | [script](verify/colored_partitions.py) | [file](OeisProofs/ColoredPartitions.lean) |

## Formalization scope

Every Lean file proves the statement that the OEIS marks as a conjecture.
Some additional claims of the written proofs are not formalized. Each proof
file gives the details in its "Formalization" section.

| Result | Proved in Lean | Proved on paper only | Lean check against OEIS data |
| --- | --- | --- | --- |
| A306598 | The sign rule, and the general theorem for strictly increasing positive sequences | The divisibility remarks | First 8 terms, kernel-checked |
| A343752 | The equivalence and the closed form | None | First 16 terms, kernel-checked |
| A372966 | Divisibility, the congruence modulo 240, and a(2) = 241 | None | Uses Mathlib's `sigma` |
| A365849 | The congruence modulo 36 | The characterization of the terms and the optimality of 36 | None; the Lean file does not define the sequence |
| A352446, A341309, A352269 | Statements 1 and 2, with Statement 1 in coefficient form | Statements 3 and 4, and the power-series form of Statement 1 | First 12 terms of A352446 and A341309, kernel-checked |
| A292042, A292043 | Both series formulas, in coefficient form | None | First 20 and 16 terms, kernel-checked |
| Colored partitions | The general theorem, as integer and as power-series identity, and the five corollaries | None | Compiled evaluation only, not kernel-checked |

All theorems depend only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. The Lean files contain no `sorry` and no `native_decide`.

## Requirements

- [elan](https://github.com/leanprover/elan), which installs the Lean version
  named in `lean-toolchain`
- Python 3
- [pre-commit](https://pre-commit.com), for contributors

## Running the checks

Download the prebuilt Mathlib files, then build the Lean project:

```
lake exe cache get
lake build
```

Run one numerical check:

```
python3 verify/<name>.py
```

Install the commit hooks one time after you clone the repository:

```
pre-commit install
```

## Adding a result

1. Copy `proofs/TEMPLATE.md` to `proofs/<entry>.md` and write the proof.
2. Add the numerical check as `verify/<entry>.py`.
3. Add the formalization as `OeisProofs/<Entry>.lean`.
4. Import the new file in `OeisProofs.lean`.
5. Add one row to the Results table.

## Status and caveats

- "Unproved" means: on the date given in the proof file, the OEIS entry showed
  the statement as conjectural and a literature search found no proof. Pending
  OEIS edits and unindexed papers are not visible to that check.
- A Lean file certifies only the formal statement that it contains. Each proof
  file says how that formal statement relates to the OEIS wording.
- No human referee has reviewed the proofs.

## Review record

| Date | Check | Result |
| --- | --- | --- |
| 2026-11-26 | One independent automated review of each written proof | No mathematical error reported; wording and scope remarks applied |
| 2026-11-27 | Automated prior-work search for each result (OEIS entries and history, arXiv, MathOverflow, journals) | No published proof found; classical sources added to each proof file |
| 2026-11-27 | Automated comparison of each Lean statement with the written theorem and the OEIS wording | Main statements match; gaps recorded under "Formalization scope" |
| 2026-11-27 | `lake build`, axiom audit of all theorems, and all scripts in `verify/` | All pass |

## How to cite

See [CITATION.cff](CITATION.cff).

## License

The content of this repository is licensed under the
[Apache License 2.0](LICENSE).
