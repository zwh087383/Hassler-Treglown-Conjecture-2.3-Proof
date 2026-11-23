#!/usr/bin/env python3
"""Render the main TeX manuscript and all proof appendices to one PDF.

Requirements: pandoc, reportlab, pymupdf, matplotlib, pillow, fonttools.
The exact mathematics is in the TeX and plain-text proof files; this is
an offline presentation builder, not a mathematical verifier.
"""
from pathlib import Path
from io import BytesIO
import hashlib
import html
import json
import os
import re
import subprocess
import textwrap

import fitz
import matplotlib
matplotlib.use("Agg")
from matplotlib import mathtext, font_manager
from fontTools.pens.recordingPen import DecomposingRecordingPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont as FontFile
from PIL import Image as PILImage
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle,
    PageBreak, Preformatted,
)
from reportlab.platypus.tableofcontents import TableOfContents
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
# ReportLab honors SOURCE_DATE_EPOCH. The default is the manuscript's date in UTC.
os.environ.setdefault("SOURCE_DATE_EPOCH", "1795305600")
ASSETS = HERE / "complete_render_assets"
ASSETS.mkdir(exist_ok=True)
OUT = ROOT / "output"
OUT.mkdir(exist_ok=True)
font = ASSETS / "cjk.ttf"


def write_proof_font(destination):
    """Complete the CJK font with the two math glyphs used in Appendix S1."""
    original = fitz.Font("china-s").buffer
    with FontFile(BytesIO(original), recalcTimestamp=False) as base:
        missing = [ord(symbol) for symbol in "−↦" if ord(symbol) not in base.getBestCmap()]
        if not missing:
            destination.write_bytes(original)
            return
        glyph_order = list(base.getGlyphOrder())
        default_glyph = glyph_order[0]
        advance = base["hmtx"][default_glyph][0]
        with FontFile(font_manager.findfont("DejaVu Sans")) as donor:
            donor_glyphs = donor.getGlyphSet()
            scale = base["head"].unitsPerEm / donor["head"].unitsPerEm
            # Donor outlines are from DejaVu Sans. The original notices are also
            # distributed in licenses/DejaVu-LICENSE.txt beside the manuscript.
            for name_id in (0, 13, 14):
                donor_notice = donor["name"].getDebugName(name_id)
                if donor_notice:
                    original_notice = base["name"].getDebugName(name_id)
                    notices = [original_notice] if original_notice else []
                    notices.append("DejaVu Sans, supplemental math glyphs only:\n" + donor_notice)
                    base["name"].setName("\n".join(notices), name_id, 3, 1, 0x409)
            for codepoint in missing:
                donor_name = donor.getBestCmap()[codepoint]
                donor_advance, donor_bearing = donor["hmtx"][donor_name]
                # Preserve the advance used in the original text so neighboring glyphs stay put.
                offset = (advance - scale * donor_advance) / 2
                outline = DecomposingRecordingPen(donor_glyphs)
                donor_glyphs[donor_name].draw(outline)
                pen = TTGlyphPen(None)
                outline.replay(TransformPen(pen, (scale, 0, 0, scale, offset, 0)))
                name = f"proofUni{codepoint:04X}"
                base["glyf"][name] = pen.glyph()
                base["hmtx"][name] = (advance, round(scale * donor_bearing + offset))
                if "vmtx" in base:
                    base["vmtx"][name] = base["vmtx"][default_glyph]
                glyph_order.append(name)
                for table in base["cmap"].tables:
                    if table.isUnicode() and table.format in (4, 12):
                        table.cmap[codepoint] = name
        base.setGlyphOrder(glyph_order)
        base.save(destination)


write_proof_font(font)
pdfmetrics.registerFont(TTFont("CJK", str(font)))
pdfmetrics.registerFontFamily("CJK", normal="CJK", bold="CJK", italic="CJK", boldItalic="CJK")
mono_path = font_manager.findfont("DejaVu Sans Mono")
pdfmetrics.registerFont(TTFont("ProofMono", mono_path))
WIDTH = A4[0] - 106
INK = colors.HexColor("#173C54")
styles = {
    "body": ParagraphStyle("body", fontName="CJK", fontSize=10.2, leading=19.5,
        textColor=colors.HexColor("#20313D"), spaceAfter=7, splitLongWords=True),
    "title": ParagraphStyle("title", fontName="CJK", fontSize=21, leading=32,
        alignment=1, textColor=INK, spaceAfter=12),
    "subtitle": ParagraphStyle("subtitle", fontName="CJK", fontSize=12.5, leading=24,
        alignment=1, textColor=INK, spaceAfter=10),
    "meta": ParagraphStyle("meta", fontName="CJK", fontSize=9.5, leading=18,
        alignment=1, textColor=colors.HexColor("#617786"), spaceAfter=18),
    "h1": ParagraphStyle("h1", fontName="CJK", fontSize=13.5, leading=23,
        textColor=INK, spaceBefore=16, spaceAfter=9, keepWithNext=True),
    "h2": ParagraphStyle("h2", fontName="CJK", fontSize=11.6, leading=20,
        textColor=INK, spaceBefore=10, spaceAfter=7, keepWithNext=True),
    "small": ParagraphStyle("small", fontName="CJK", fontSize=8.5, leading=15.5,
        textColor=colors.HexColor("#476071"), spaceAfter=8, splitLongWords=True),
    "proof": ParagraphStyle("proof", fontName="ProofMono", fontSize=8.8,
        leading=12.6, textColor=colors.HexColor("#253744"), spaceAfter=0),
    "proof_cjk": ParagraphStyle("proof_cjk", fontName="CJK", fontSize=9.5,
        leading=14.0, textColor=colors.HexColor("#253744"), spaceAfter=0),
}
cache = {}
story = []
counters = {"section": 0, "anchor": 0}
render_log = {"appendices": []}


def equation(src, size=10.5):
    src = re.sub(r"\\tag\{[^}]*\}", "", src)
    src = re.sub(r"\\(?:bigl|bigr|Bigl|Bigr)\b", "", src)
    src = src.replace(r"\displaystyle", "")
    src = src.replace(r"\text{或}", r"\mathrm{or}")
    src = src.replace(r"\mathbin{\square}", r"\square")
    src = src.replace(r"\square", r"\,□\,")
    src = src.replace(r"\lor", r"\vee")
    src = re.sub(r"\\ge(?![A-Za-z])", r"\\geq", src)
    src = re.sub(r"\\le(?![A-Za-z])", r"\\leq", src)
    src = re.sub(r"\\ne(?![A-Za-z])", r"\\neq", src)
    src = re.sub(r"\\(mathbb|mathcal|boldsymbol|mathbf|mathrm|mathsf)\s+([A-Za-z])", r"\\\1{\2}", src)
    src = re.sub(r"\\frac\s+([A-Za-z0-9])", r"\\frac{\1}", src)
    src = re.sub(r"\\frac([A-Za-z0-9])([A-Za-z0-9])", r"\\frac{\1}{\2}", src)
    src = src.replace(r"\binom Nj", r"\binom{N}{j}")
    src = " ".join(src.split())
    key = (src, size)
    if key not in cache:
        path = ASSETS / (hashlib.sha256(repr(key).encode()).hexdigest()[:20] + ".png")
        if not path.exists():
            mathtext.math_to_image("$" + src + "$", str(path),
                prop=font_manager.FontProperties(size=size), dpi=240,
                format="png", color="#173C54")
        with PILImage.open(path) as im:
            w, h = im.size
        cache[key] = (path, w * 72 / 240, h * 72 / 240)
    return cache[key]


def inline(nodes):
    out = []
    for node in nodes:
        typ, c = node["t"], node.get("c")
        if typ == "Str":
            out.append(html.escape(c))
        elif typ in ("Space", "SoftBreak"):
            out.append(" ")
        elif typ == "LineBreak":
            out.append("<br/>")
        elif typ in ("Strong", "Emph"):
            out.append('<font color="#173C54">' + inline(c) + '</font>')
        elif typ == "Span":
            out.append(inline(c[1]))
        elif typ == "Math":
            path, w, h = equation(c[1])
            if w > WIDTH - 12:
                raise ValueError("Inline formula too long: " + c[1])
            out.append(f'<img src="{path}" width="{w:.3f}" height="{h:.3f}" valign="middle"/>')
        elif typ == "Link":
            out.append(inline(c[1]))
        elif typ == "Quoted":
            out.append("“" + inline(c[1]) + "”")
        elif typ == "Code":
            out.append(html.escape(c[1]))
        elif typ != "RawInline":
            raise ValueError(node)
    result = "".join(out)
    return re.sub(r'(<img [^>]+/>)([，。；：！？、）]+)', r'<nobr>\1\2</nobr>', result)


def para(nodes, style="body"):
    current = []
    for node in nodes:
        if node["t"] == "Math" and node["c"][0]["t"] == "DisplayMath":
            if current and inline(current).strip():
                story.append(Paragraph(inline(current), styles[style]))
            current = []
            path, w, h = equation(node["c"][1], 11.4)
            scale = min(1, (WIDTH - 14) / w)
            obj = Image(str(path), width=w * scale, height=h * scale)
            obj.hAlign = "CENTER"
            story.extend((Spacer(1, 5), obj, Spacer(1, 9)))
        else:
            current.append(node)
    if current and inline(current).strip():
        story.append(Paragraph(inline(current), styles[style]))


def heading(title, level=0):
    p = Paragraph(html.escape(title), styles["h1" if level == 0 else "h2"])
    p.outline_title = title
    p.outline_level = level
    counters["anchor"] += 1
    p.outline_key = "proof-" + str(counters["anchor"])
    story.append(p)


def blocks(items):
    for item in items:
        typ, c = item["t"], item.get("c")
        if typ in ("Para", "Plain"):
            para(c)
        elif typ == "Header":
            text = "".join(x.get("c", " ") if x["t"] == "Str" else " " for x in c[2])
            if c[0] == 1:
                counters["section"] += 1
                text = str(counters["section"]) + ". " + text
                heading(text)
            else:
                heading(text, 1)
        elif typ == "Div":
            blocks(c[1])
        elif typ == "OrderedList":
            for i, contents in enumerate(c[1], 1):
                for child in contents:
                    if child["t"] in ("Para", "Plain"):
                        para([{"t": "Str", "c": str(i) + ". "}] + child["c"])
                    else:
                        blocks([child])
        elif typ == "BulletList":
            for contents in c:
                for child in contents:
                    if child["t"] in ("Para", "Plain"):
                        para([{"t": "Str", "c": "• "}] + child["c"])
                    else:
                        blocks([child])
        elif typ != "RawBlock":
            raise ValueError(typ)


def cleaned_proof(path):
    """Omit only unused historical sections/status prose, never proof steps."""
    text = path.read_text(encoding="utf-8")
    if path.name == "paper_algebra_lowrank.txt":
        text = text.split("纯零层时可更强.", 1)[0]
        text = text.replace("本文不证明原渐近猜想，也不证明一般分块矩阵猜想。\n", "")
        text = text.replace("新颖性未核查。\n", "")
    elif path.name == "colored_dd_proof.txt":
        text = text.split("The remaining general proof problem still includes", 1)[0]
    elif path.name == "global_general_potential_audit.txt":
        text = text.split("ADDITIONAL AUDIT FOR ZERO-AGENT", 1)[0]
        text = text.replace(
            "The exceptional finite core\nstill needs the previously established bounded-rank/core argument;\n"
            "this statement alone does not erase that core or complete the original\nsum-free-set conjecture.",
            "The exceptional finite core is handled in Appendix G of the complete proof.")
    elif path.name == "global_final_bridge_audit.txt":
        text = text.split("(d) Optional stronger structure sources", 1)[0]
    elif path.name == "matrix_nozero_remaining.txt":
        text = text.replace(" (or the older BDD\n    certificate)", "")
    return text.strip() + "\n"


def wrap_literal(text, style):
    font_name, size = style.fontName, style.fontSize
    result = []
    for line in text.expandtabs(4).splitlines():
        if not line:
            result.append("")
            continue
        while pdfmetrics.stringWidth(line, font_name, size) > WIDTH - 8:
            lo, hi = 1, len(line)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if pdfmetrics.stringWidth(line[:mid], font_name, size) <= WIDTH - 8:
                    lo = mid
                else:
                    hi = mid - 1
            cut = lo
            if not re.search(r"[\u3400-\u9fff]", line):
                space = line.rfind(" ", 0, cut + 1)
                if space >= cut // 2:
                    cut = space + 1
            result.append(line[:cut].rstrip())
            line = "    " + line[cut:].lstrip()
        result.append(line)
    return "\n".join(result)


src = (HERE / "complete_manuscript.tex").read_text(encoding="utf-8")
body = src.split(r"\begin{document}", 1)[1].rsplit(r"\end{document}", 1)[0]
source_path = ASSETS / "body.tex"
source_path.write_text(body, encoding="utf-8")
res = subprocess.run(["pandoc", str(source_path), "-f", "latex", "-t", "json"],
    text=True, encoding="utf-8", capture_output=True, check=True)
document = json.loads(res.stdout)
for first, style in zip(document["blocks"][:3], ("title", "subtitle", "meta")):
    para(first["c"], style)
story.append(Paragraph(
    "本稿收录主证明及 25 份技术附录。配套 Lean 工程已形式化验证主定理。"
    "最后三类局部模型采用全秩熵证明，部分局部步骤另附精确有限证书及验证程序。",
    styles["body"]))
story.append(Spacer(1, 15))
story.append(Paragraph("目录", styles["h1"]))
toc = TableOfContents()
toc.levelStyles = [
    ParagraphStyle("TOC0", fontName="CJK", fontSize=9.4, leading=16.0,
        leftIndent=0, firstLineIndent=0, textColor=INK, spaceBefore=3),
    ParagraphStyle("TOC1", fontName="CJK", fontSize=8.5, leading=14.0,
        leftIndent=14, firstLineIndent=0, textColor=colors.HexColor("#476071")),
]
story.append(toc)
story.append(PageBreak())
blocks(document["blocks"][3:])

appendices = json.loads((HERE / "appendix_manifest.json").read_text(encoding="utf-8"))
for code, title, relative in appendices:
    path = ROOT / relative
    proof = cleaned_proof(path)
    story.append(PageBreak())
    heading("附录 " + code + " · " + title)
    story.append(Paragraph("证明来源：" + html.escape(relative), styles["small"]))
    if code == "S1":
        story.append(Paragraph("收录第 0--8 节所需证明；省略其后未使用的推广与历史进展文字。", styles["small"]))
    else:
        story.append(Paragraph("以下保留证明原有记号。N、n、q 等局部符号以本附录的定义为准。", styles["small"]))
    style = styles["proof_cjk"] if re.search(r"[\u3400-\u9fff]", proof) else styles["proof"]
    wrapped = wrap_literal(proof, style)
    story.append(Preformatted(wrapped, style, dedent=0))
    render_log["appendices"].append({"id": code, "source": relative,
        "rendered_lines": len(wrapped.splitlines())})


class ProofDoc(SimpleDocTemplate):
    def afterFlowable(self, flowable):
        if hasattr(flowable, "outline_title"):
            title = flowable.outline_title
            key = flowable.outline_key
            level = flowable.outline_level
            self.canv.bookmarkPage(key)
            self.canv.addOutlineEntry(title, key, level=level, closed=True)
            self.notify("TOCEntry", (level, title, self.page, key))


def footer(canvas, doc):
    canvas.setStrokeColor(colors.HexColor("#D4DFE5"))
    canvas.line(53, 39, A4[0] - 53, 39)
    canvas.setFont("CJK", 8)
    canvas.setFillColor(colors.HexColor("#627A89"))
    canvas.drawString(53, 25, "完整证明草稿 · 2026-11-22 · 公开修订稿")
    canvas.drawRightString(A4[0] - 53, 25, str(doc.page))


pdf = OUT / "sumfree_complete_proof_draft.pdf"
doc = ProofDoc(str(pdf), pagesize=A4, leftMargin=53, rightMargin=53,
    topMargin=44, bottomMargin=53, title="极大无和集计数：完整证明草稿",
    author="Research proof dossier")
doc.multiBuild(story, onFirstPage=footer, onLaterPages=footer)
render_log.update({"pdf": pdf.relative_to(ROOT).as_posix(), "math_assets": len(cache),
    "pages": len(fitz.open(pdf))})
(HERE / "complete_render_log.json").write_text(json.dumps(render_log, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k:v for k,v in render_log.items() if k != "appendices"}, ensure_ascii=False))
