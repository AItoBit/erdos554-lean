# Erdős 554: conditional analytic comparison

This project proves a conditional implication for sequences with the bounds relevant to Erdős 554. It does not solve the full problem or prove the combinatorial bounds used as hypotheses.

For fixed n >= 4 and c > 0, if nonnegative f(k) is eventually at most (4n)^k k^(k/n) and g(k) is eventually at least (c k^(1/3) / log k)^k, then f(k)/g(k) tends to zero. The proof uses the positive exponent gap 1/3 - 1/n. It does not apply to n = 2 or n = 3.

The cycle Ramsey upper bound is from Axenovich, Cames van Batenburg, Janzer, Michel, and Rundström, https://arxiv.org/abs/2510.17981. The triangle lower-bound shape is recorded in https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean. These results motivate the hypotheses; they are not imported or assumed as hidden axioms.

Lean 4.33.1, Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Build with `lake exe cache get` followed by `lake --wfail build`. The source prints the axioms of all principal declarations. Verification is in progress.
