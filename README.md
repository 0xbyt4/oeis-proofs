# oeis-proofs

Proofs of open conjectures recorded in the On-Line Encyclopedia of Integer
Sequences (OEIS).

Many OEIS entries carry statements marked "Conjecture", "Apparently" or
"Empirical". This repository collects proofs of such statements. Each result
has a written proof, a numerical check and, where practical, a Lean 4
formalization.

## Method

For every statement we do these steps:

1. Check that the OEIS entry still lists the statement as unproved.
2. Search the literature for an existing proof.
3. Test the statement numerically with a dependency-free Python script.
4. Write a complete human-readable proof.
5. Formalize the proof in Lean 4 with Mathlib where that is practical.

## Layout

| Path | Content |
| --- | --- |
| `proofs/` | One Markdown file per result, with statement, proof and remarks |
| `verify/` | Numerical checks, Python 3 standard library only |
| `OeisProofs/` | Lean 4 formalizations, one file per result |
| `OeisProofs.lean` | Root module that imports every formalization |

## Results

No results are published yet. Each result gets one row in this table.

| OEIS entry | Statement | Proof | Numerical check | Lean |
| --- | --- | --- | --- | --- |

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

- "Open" means: on the date given in the proof file, the OEIS entry showed the
  statement as conjectural and a literature search found no proof.
- A Lean file certifies only the formal statement that it contains. Each proof
  file says how that formal statement relates to the OEIS wording.

## License

The content of this repository is licensed under the
[Apache License 2.0](LICENSE).
