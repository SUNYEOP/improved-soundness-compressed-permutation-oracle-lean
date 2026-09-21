# ProofAtlas hook-length formula source

This directory preserves the original Apache-2.0 source and its accompanying
license, copyright notice and upstream evidence. `Basic.lean` is byte-for-byte
the published source. It is not itself part of this project's Lean import graph.

- Theorem page: https://www.proofatlas.ai/formalizations/hook-length-formula/
- Source page: https://www.proofatlas.ai/sources/hook-length-formula/
- Pinned package commit: `7e628b6361f20e33d6b8214adc608685b9d4da2d`
- Original path: `AtlasKnownTheorems/HookLengthFormula/Basic.lean`
- Original SHA-256: `bfcd609759bb37494f274922f11b212beaae2dce56da4e197912ced7915089a6`
- Copyright: 2026 Advameg, Inc.; see `NOTICE` and `LICENSE`.
- Upstream checker toolchain: Lean 4.29.1, as recorded in `evidence.json`.

The source URL is the source page followed by
`commits/7e628b6361f20e33d6b8214adc608685b9d4da2d/AtlasKnownTheorems/HookLengthFormula/Basic.lean`.
The license, notice and evidence were downloaded from the same pinned directory.
The original source hash was checked before making the local adaptation.

## Local adaptation

The adapted [hook-length module](../../../QuantumOracle/Proof/HookLengthFormula.lean)
preserves the upstream namespace, definitions, and mathematical statements and
uses the project's pinned Lean/mathlib 4.32.2 environment. The adaptation:

- Supplies classical decidability and finite instances for corner subtypes.
- Uses the current finite-surjectivity API and makes product order and
  corner-column definitions explicit where required by elaboration.
- Uses the locally proved
  [`HookLengthCompat.coeff_eq_sum`](../../../QuantumOracle/Proof/HookLengthCompat.lean),
  derived from Lagrange interpolation and polynomial leading coefficients.
- Retains the original copyright and Apache-2.0 identifiers.

The original source, license, notice, and checker evidence remain unchanged.
The project's [proof checker](../../../docs/REPRODUCIBILITY.md) compiles and audits
the adapted module together with the rest of the proof.

## Mathematical scope

The hook-length theorem identifies the product of hook lengths times the number
of standard tableaux with the factorial of the diagram's size. The source also
proves the recurrence obtained by removing the maximum-entry corner.
[`YoungHookRatio`](../../../QuantumOracle/Proof/YoungHookRatio.lean) derives the
tableau-count ratios used by the soundness proof.

The connections to Specht dimensions, restriction decompositions, and the oracle
Gram spectrum are proved in the project's representation, Gram, and conditioning
modules; see the [proof map](../../../docs/PROOF_MAP.md).
