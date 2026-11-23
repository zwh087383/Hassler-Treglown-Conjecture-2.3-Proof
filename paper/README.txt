极大无和集计数：完整证明草稿与精确证书
============================================================
公开修订稿 · 2026-11-22

主结论
  对 n=5^k，f_max(F_5^k)=3^(n/10+o(n))，k趋于无穷。
  f_max按包含关系计数极大无和集；禁止x+y=z，允许重复变量。
  目标是Hassler--Treglown的Conjecture 2.3。

当前状态
  完整纸面证明草稿，包含全部种子类型、统一全局误差、上下界。
  已完成内部交叉审阅，以及18个精确有限证书检查。
  本稿配套的 Lean 工程已形式化验证主定理，定理名为 Audit.Sharp.main_theorem。
  本稿待外部同行审阅，文献优先权与新颖性仍待专门核查。

本次计数勘误（附录 C0 第 19 页、附录 S1 第 31 页）
  对两个互为相反数的非零层种子，规范化后 P=Q={0}。每个尾指标对应一个四边形，
  不同指标之间没有边，所以任意尾空间 K 的极大独立集数为 2^|K|。
  最小尾空间 K={0} 时为 2，附录 S1 所取的 K=F_5 时为 32。

阅读入口
  round5/complete_manuscript.tex       中文主稿
  round5/global_final_coverage.txt     全部种子的最终穷尽覆盖
  round5/global_final_bridge_audit.txt 容器、移除、统一常数、匹配下界
  round5/appendix_manifest.json        PDF的25份完整证明附录索引
  round5/final_verification_report.json 实际运行的精确检查及输出

随包PDF由中文主稿及25份附录组成，共113页（交付版）。
各局部证明文件中的N、n、q等符号仅在其自身定义范围内使用。
各附录及审阅记录保留成稿时对验证进度的描述。当前的形式化验证状态见上文，最终依赖以
global_final_coverage.txt为准。PDF省去了未使用的历史推广章节。

最终三个局部缺口的证明
  A: root_entropy_ac_proof.txt，Z=1259/16<81。
  C: 同文件，Z=279/4<81。
  B: matrix_typeB_entropy_proof.txt，Z=43177189/20736<3^7。
     B还包括坐标碰撞的穷尽分类、Boolean矩阵因子、212<243纸界。
  三个证明都适用于所有秩；无需大型秩二搜索DAG。

复现有限检查（Python 3标准库，无第三方依赖）
  在解压目录运行：
      python3 round5/verify_all.py
  不要使用python -O；断言是验证的一部分。
  正常结束应显示：ALL 18 FINITE CHECKS PASSED。
  转移脚本从定义重建矩阵；若干JSON是生成输出，不是信任输入。
  这 18 项程序检查局部有限计算。配套 Lean 工程给出全局主定理的形式化证明。

证明来源与审阅
  核心外部输入是Green--Ruzsa容器、Green三集合移除、Lev结构定理。
  准确陈述与URL见主稿参考文献及global_final_bridge_audit.txt。
  内部审阅记录包括：
      global_manuscript_audit.txt
      matrix_final_dependency_audit.txt
      zero_final_bridge_audit.txt
      zero_entropy_ac_audit.txt
      zero_entropy_b_audit.txt
      global_transfer_audit.txt
      zero_small_seed_audit.txt
      zero_sizefive_audit.txt

排版重建（可选，与证明验证无关）
  本版的重建环境为 Python 3.12.7、Pandoc 3.9、ReportLab 5.1.0、PyMuPDF 2.1、
  Matplotlib 3.11.2、Pillow 12.3.0 和 fontTools 4.66.0。Pandoc 须在 PATH 中。
  构建器使用 PyMuPDF 内置中文字体，并从 Matplotlib 随附的 DejaVu Sans 取数学负号和映射箭头。
  DejaVu 的版权与许可原文见 licenses/DejaVu-LICENSE.txt。补入字形的版权与许可也保存在字体的名称表中。
  PDF 的默认时间戳为修订日 2026-11-22 的 UTC 零时。可用 SOURCE_DATE_EPOCH 指定另一时间。
  运行：python3 round5/build_complete_pdf.py
  它读取主稿和附录，生成output/sumfree_complete_proof_draft.pdf。
  主稿TeX仅是主证明文本；完整证明附录由构建器按manifest加入PDF。

未纳入最终依赖的探索
  旧BDD、29份秩二决策DAG、浮点优化记录、C++探测程序均未打包。
  最终有限部分是7个百点模型的短转移证书、11个二十点分支表，
  以及势函数标量不等式和三个熵加权和的精确检查。

MANIFEST.json记录所有交付文件的SHA-256校验值。
