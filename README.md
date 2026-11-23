# Hassler–Treglown 猜想 2.3 的证明

*Proof of Hassler and Treglown’s Conjecture 2.3 on maximal sum-free sets in $\mathbb F_5^k$.*

设 $n=5^k$。在 $\mathbb F_5^k$ 中，按包含关系极大的无和集个数满足

$$f_{\max}(\mathbb F_5^k)=3^{n/10+o(n)}\qquad(k\to\infty).$$

A set is sum-free if it contains no solution to $x+y=z$, including solutions with repeated entries. It is maximal if adding any element outside the set creates such a solution. The result determines the leading exponential rate. Hassler and Treglown stated the formula as [Conjecture 2.3 and gave the matching lower-bound construction](https://arxiv.org/html/2506.17401v2#S2).

## 论文与证明

- [中文论文（PDF，含技术附录）](paper/output/sumfree_complete_proof_draft.pdf) 和 [论文源文件](paper/round5/complete_manuscript.tex)。
- [随稿有限证书的运行入口](paper/round5/verify_all.py)，涵盖 18 项检查。
- [Lean 主定理与全局上界](lean/Audit/Sharp.lean) 及[按原稿定义表述的主定理](lean/Audit/DefinitionCheck.lean)。
- [中文核验报告](lean/核验报告.md) 和[内核逐项复查记录](lean/verification/kernel-replay.log)。形式化对部分局部引理采用了另一套有限证书。

### 本版勘误

原稿第 19、31 页涉及两个互为相反数的外层种子元素。归一化为 $P=Q=\{0\}$ 后，每个尾坐标对应一个四边形，它们之间没有边。每个四边形有两个极大独立集，因此尾空间为 $K$ 时，整个通用块恰有 $2^{|K|}$ 个极大独立集。最小块有 2 个，$K=\mathbb F_5$ 时有 32 个。这一计数满足主证明所需的上界 $3^{|K|}$。

## Reproduce the checks

From the repository root, use Python 3.10 or later to run the paper's finite checks and the independent counts. These programs use the Python standard library. On systems where the executable is named `python3`, use that command in place of `python`.

```sh
python -B paper/round5/verify_all.py
python -B lean/independent_counts.py
```

With Lean's `elan` and `lake` available, run the following commands. The project pins Lean 4.19.0 and a specific mathlib revision in [the dependency lockfile](lean/lake-manifest.json).

```sh
cd lean
lake exe cache get
lake build Audit
lake env lean -t0 Audit.lean
lake env lean --run verification/KernelReplay.lean Audit Audit.Sharp.main_theorem Audit.Sharp.upper Audit.Sharp.log_limit Audit.Sharp.limit_via_generic_blocks Audit.GenericTheorem.generic_block Audit.DefinitionCheck.paper_statement Audit.Raw.type_A Audit.Raw.type_B Audit.Raw.type_C
```

The recorded builds ran on Windows. The kernel replay checked 3,042 project declarations, including 1,762 theorems. The main theorem uses `propext`, `Classical.choice`, `Quot.sound` and `Lean.ofReduceBool`. The last of these trusts Lean's compiler for native finite computations. Input hashes in the [Lean verification record](lean/verification/verification.json) identify the manuscript supplied before the erratum. The [revised paper manifest](paper/MANIFEST.json) identifies the files of this edition.

To verify the archived Lean files with GNU `sha256sum`, run this command from `lean/`. The original checksum list uses Windows line endings.

```sh
sed 's/\r$//' verification/SHA256SUMS.txt | sha256sum -c -
```
