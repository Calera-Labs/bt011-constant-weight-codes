# Thirty-six improved lower bounds for A(n, 4, w)

Casey Lee Race  
Calera Labs  
support@caleralabs.com  
ORCID [0009-0006-5237-1112](https://orcid.org/0009-0006-5237-1112)

This repository holds the preprint and the certificates for 36 improved lower bounds on the binary constant-weight numbers A(n, 4, w), for 24 ≤ n ≤ 30 and 7 ≤ w ≤ 15. Each bound is strictly larger than the value in Andries E. Brouwer's table at <https://aeb.win.tue.nl/codes/Andw.html> as fetched on 24 November 2026, 22:50 CET.

The constructions, the Lean 4 distance lemmas, and the Python verifier are self-contained. Checking the codes does not require any other software from Calera.

## Check the codes

Python 3 is enough. There are no third-party packages.

```bash
python3 verify_bt011_standalone.py
```

The verifier rebuilds all 36 codes (38,467,121 codewords) from the compact certificates, checks that every code has minimum distance at least 4, checks the five explicit hexadecimal codeword files, and matches the SHA-256 digests in `results/bt011_proven_36_world_records.json`. On one core this takes about half a minute.

## What is in this repository

| Path | Role |
|---|---|
| `preprint/` | Paper source and `main.pdf` |
| `lean/BT011_AsymmetricBSSS.lean` | Lean 4.33.0 distance lemmas, plus an arithmetic check of the 36 printed summary rows |
| `results_asym/asym_*.json` | 16 new asymmetric truncated-support packings |
| `results_asym/bt011_candidate_records_spec.json` | Term-by-term assembly of the 36 codes |
| `results_pk/*.pk` | 4 new partitions on n = 14 and n = 16 |
| `results/bt011_A_*.hex` | Five explicit codeword files, for the codes with at most 75,000 words |
| `results/bt011_proven_36_world_records.json` | Sizes, prior bounds, and SHA-256 digests of the 36 codes |
| `corpora/ls13_ls15.json` | Explicit large sets LS(13) and LS(15) |
| `corpora/brouwer_2010_pk/` | The 42 baseline partitions from Brouwer's 22 March 2010 archive that these codes use |
| `verify_bt011_standalone.py` | Independent pure-Python verifier |

The Lean file checks the distance argument and the printed totals (36 rows, gain +16,697, 38,467,121 codewords, and the sum of w times size). It does not inspect the codewords. The codewords are certified by `verify_bt011_standalone.py`.

## Baseline partitions

The files in `corpora/brouwer_2010_pk/` come from Andries E. Brouwer's public partition archive of 22 March 2010:

<https://aeb.win.tue.nl/codes/partitions/>

See `corpora/brouwer_2010_pk/SOURCE.txt`. Those files are included so the 36 codes can be rebuilt. They are his work.

## Contact

support@caleralabs.com
