#!/usr/bin/env python3
import argparse
import html
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path


@dataclass(frozen=True)
class Section:
    heading: str
    paragraphs: list[str]
    snippet: str | None = None


@dataclass(frozen=True)
class Issue:
    issue_date: date
    volume: int
    number: int
    price_cents: int
    kicker: str
    headline: str
    deck: str
    byline: str
    opening: str
    pull_quote: str
    pull_attr: str
    notice_label: str
    notice_code: str
    sections: list[Section]
    footer: str


DEFAULT_ISSUE = Issue(
    issue_date=date(2026, 6, 25),
    volume=1,
    number=1,
    price_cents=13,
    kicker="Latest Release",
    headline="Ownership Lands, the Middle End Gets Real, and the Editor Learns a Few Tricks",
    deck=(
        "Talk 0.1.13 tightens the ownership checker, moves lowering onto a MIR-shaped path, "
        "and keeps polishing the language server and runtime edges."
    ),
    byline="By the Compiler Desk - Special to Users",
    opening=(
        "Talk's latest release is less about fireworks and more about foundations: the compiler "
        "now has a firmer place to reason about ownership, lowering has a semantic middle form to "
        "stand on, and everyday tooling picked up the kind of fixes that make a small language feel "
        "less like a science project and more like a workshop."
    ),
    pull_quote="Ownership checking, MIR lowering, better rename support, and sharper runtime rendering.",
    pull_attr="The day's release, in one line",
    notice_label="Landing in This Release",
    notice_code='''// Ownership is now checked before lowering.
struct Counter {
  let value: Int
}

func bump(counter: Counter) {
  // The checker keeps moves and borrows honest
  // before the VM ever sees bytecode.
  counter.value + 1
}''',
    sections=[
        Section(
            "Ownership Gets Teeth",
            [
                "The big-ticket work is the ownership checker. Talk now has a dedicated pass for "
                "tracking moves, borrows, and use-after-move style mistakes before lowering. That "
                "keeps value semantics close to the source language instead of asking a later IR to "
                "reconstruct what the programmer meant.",
                "The checker also learned more about replacement, drops, and the small corners where "
                "a language with structs, methods, closures, and effects can otherwise lose track of "
                "who owns what.",
            ],
        ),
        Section(
            "A Middle Form for the Messy Middle",
            [
                "Lowering continued its move onto a semantic MIR. Blocks, branches, loops, returns, "
                "handler scopes, and statement order now have a clearer representation before they "
                "become lambda-G and bytecode. The payoff is not just cleaner internals: it gives the "
                "compiler one obvious place to answer control-flow questions.",
                "That work also makes future borrow checking and drop elaboration less magical. Source "
                "constructs stay source-shaped long enough for the compiler to reason about them, then "
                "get lowered when the answer is known.",
            ],
        ),
        Section(
            "Renames Grow Up",
            [
                "The language server's rename support got a round of attention. That is not glamorous, "
                "but it is the difference between a demo and an editor loop: symbols need to move safely "
                "when the program changes shape.",
            ],
        ),
        Section(
            "Runtime Output Reads More Like Talk",
            [
                "VM rendering picked up fixes so values printed from interpreted programs stay closer "
                "to Talk syntax. The result is better REPL feedback, better examples, and fewer moments "
                "where the implementation leaks through the interface.",
            ],
        ),
        Section(
            "Parsing and Types Keep Tightening",
            [
                "Parser and type-system tests grew around edge cases in function syntax, variants, and "
                "unification. None of those changes want a parade; all of them keep the next feature from "
                "being built on sand.",
            ],
        ),
        Section(
            "Briefly Noted",
            [
                "The release also includes assorted clippy cleanups, version bumps, more VM tests, and "
                "small fixes across lambda-G evaluation and type generation. It is a foundations release: "
                "the kind that makes the next visible feature easier to ship."
            ],
        ),
    ],
    footer="The Daily Talk - What's New in Talk - Release Notes for June 25, 2026",
)


CSS = r'''
  :root {
    --ink: #111111;
    --paper: #fbfaf7;
    --rule: #111111;
    --muted: #555049;
    --spot: #7a2f93;
    --hair: #cdc8bd;
    --notice-bg: #f4f1ea;
    --code-bg: rgba(122,47,147,0.08);
    --grain: rgba(0,0,0,0.018);
  }

  @media (prefers-color-scheme: dark) {
    :root {
      --ink: #e8e4da;
      --paper: #16140f;
      --rule: #e8e4da;
      --muted: #a59f93;
      --spot: #d68af0;
      --hair: #3a352c;
      --notice-bg: #211e17;
      --code-bg: rgba(214,138,240,0.12);
      --grain: rgba(255,255,255,0.02);
    }
  }

  * { box-sizing: border-box; }

  body {
    margin: 0;
    background: var(--paper);
    color: var(--ink);
    font-family: Georgia, "Times New Roman", "Iowan Old Style", serif;
    line-height: 1.5;
    background-image: radial-gradient(var(--grain) 1px, transparent 1px);
    background-size: 3px 3px;
  }

  .sheet { max-width: 1040px; margin: 0 auto; padding: 28px 40px 64px; }
  .masthead { text-align: center; }
  .masthead .topline {
    display: flex; justify-content: center; align-items: center;
    font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 11px; letter-spacing: 1.5px; text-transform: uppercase;
    color: var(--muted); border-bottom: 1px solid var(--ink); padding-bottom: 6px;
  }
  .masthead h1 {
    font-family: "Times New Roman", Georgia, serif; font-weight: 900;
    font-size: clamp(52px, 11vw, 104px); line-height: 0.92;
    margin: 14px 0 6px; letter-spacing: -2px;
  }
  .masthead .sub {
    font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 12px; letter-spacing: 4px; text-transform: uppercase; color: var(--muted);
  }
  .masthead .dateline {
    display: flex; align-items: center; margin-top: 14px;
    border-top: 3px double var(--ink); border-bottom: 3px double var(--ink);
    padding: 6px 2px; font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 11px; letter-spacing: 1px; text-transform: uppercase; color: var(--muted);
  }
  .masthead .dateline > span { flex: 1; }
  .masthead .dateline > span:first-child { text-align: left; }
  .masthead .dateline > span:nth-child(2) { text-align: center; }
  .masthead .dateline .price { color: var(--spot); font-weight: 700; text-align: right; }

  .lead-head { text-align: center; padding: 26px 0 10px; }
  .lead-head .kicker {
    font-family: ui-sans-serif, system-ui, sans-serif; text-transform: uppercase;
    letter-spacing: 3px; font-size: 12px; color: var(--spot); font-weight: 700; margin-bottom: 10px;
  }
  .lead-head h2 {
    font-weight: 900; font-size: clamp(30px, 5.4vw, 50px); line-height: 1.04;
    margin: 0 auto 12px; max-width: 17ch; letter-spacing: -0.5px;
  }
  .lead-head .deck { font-style: italic; color: var(--muted); font-size: 17px; max-width: 60ch; margin: 0 auto; }
  .lead-head .byline {
    font-family: ui-sans-serif, system-ui, sans-serif; font-size: 11px;
    letter-spacing: 1px; text-transform: uppercase; color: var(--muted); margin-top: 14px;
  }
  hr.thin { border: 0; border-top: 1px solid var(--ink); margin: 0; }

  .columns {
    column-count: 3; column-gap: 30px; column-rule: 1px solid var(--hair);
    margin-top: 22px; text-align: justify; hyphens: auto;
  }
  @media (max-width: 860px) { .columns { column-count: 2; } }
  @media (max-width: 560px) { .columns { column-count: 1; } }

  .columns p { margin: 0 0 11px; font-size: 15px; }
  .columns p.first { text-indent: 0; }
  .columns p:not(.first):not(.after-head) { text-indent: 1.2em; }
  .columns p.first::first-letter {
    float: left; font-weight: 900; font-size: 64px; line-height: 0.74;
    padding: 4px 8px 0 0; color: var(--spot);
  }
  .col-head {
    break-after: avoid; font-family: ui-sans-serif, system-ui, sans-serif;
    font-weight: 800; font-size: 12px; letter-spacing: 1.5px; text-transform: uppercase;
    margin: 16px 0 8px; padding-bottom: 4px; border-bottom: 1px solid var(--ink);
  }
  .after-head { text-indent: 0; }
  .snip, .notice {
    break-inside: avoid; margin: 6px 0 12px; padding: 8px 11px;
    background: var(--code-bg); border: 1px solid var(--hair); border-left: 3px solid var(--spot);
    border-radius: 3px; font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
    font-size: 11.5px; line-height: 1.5; text-align: left; hyphens: none; overflow-wrap: anywhere;
  }
  .columns code, .pull code, .fineprint code {
    font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 0.84em;
    background: var(--code-bg); border: 1px solid var(--hair); border-radius: 3px; padding: 0 4px;
  }
  .pull {
    break-inside: avoid; border-top: 3px double var(--ink); border-bottom: 3px double var(--ink);
    padding: 14px 0; margin: 6px 0 14px; text-align: center;
  }
  .pull q { font-style: italic; font-size: 20px; line-height: 1.35; quotes: "\201C" "\201D"; }
  .pull .attr {
    display: block; margin-top: 8px; font-family: ui-sans-serif, system-ui, sans-serif;
    font-size: 11px; letter-spacing: 1px; text-transform: uppercase; color: var(--muted);
  }
  .notice { border-left: 1px solid var(--ink); padding: 12px 14px; background: var(--notice-bg); }
  .notice .label {
    font-family: ui-sans-serif, system-ui, sans-serif; font-size: 10px; letter-spacing: 2px;
    text-transform: uppercase; color: var(--spot); font-weight: 700; margin-bottom: 8px;
    text-align: center; border-bottom: 1px solid var(--hair); padding-bottom: 6px;
  }
  .notice pre { margin: 0; white-space: pre-wrap; text-align: left; hyphens: none; font-family: ui-monospace, Menlo, Consolas, monospace; font-size: 11.5px; line-height: 1.55; color: var(--ink); }
  .fineprint {
    margin-top: 28px; border-top: 3px double var(--ink); padding-top: 12px; text-align: center;
    font-family: ui-sans-serif, system-ui, sans-serif; font-size: 11px; letter-spacing: 1px;
    text-transform: uppercase; color: var(--muted);
  }
'''


def html_paragraph(text: str, class_name: str | None = None) -> str:
    class_attr = f' class="{class_name}"' if class_name else ""
    return f"<p{class_attr}>{html.escape(text)}</p>"


def render_issue(issue: Issue) -> str:
    day = issue.issue_date.strftime("%A, %B %-d, %Y")
    safe_title = f"The Daily Talk - {issue.issue_date.isoformat()}"
    body_parts: list[str] = [html_paragraph(issue.opening, "first")]

    midpoint = max(1, len(issue.sections) // 2)
    for index, section in enumerate(issue.sections):
        if index == midpoint:
            body_parts.append(
                "<div class=\"notice\">"
                f"<div class=\"label\">{html.escape(issue.notice_label)}</div>"
                f"<pre>{html.escape(issue.notice_code)}</pre>"
                "</div>"
            )
        body_parts.append(f"<div class=\"col-head\">{html.escape(section.heading)}</div>")
        for para_index, paragraph in enumerate(section.paragraphs):
            body_parts.append(html_paragraph(paragraph, "after-head" if para_index == 0 else None))
        if section.snippet:
            body_parts.append(f"<div class=\"snip\">{html.escape(section.snippet).replace(chr(10), '<br>')}</div>")
        if index == 1:
            body_parts.append(
                "<div class=\"pull\">"
                f"<q>{html.escape(issue.pull_quote)}</q>"
                f"<span class=\"attr\">- {html.escape(issue.pull_attr)}</span>"
                "</div>"
            )

    return f'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(safe_title)}</title>
<style>{CSS}</style>
</head>
<body>
<div class="sheet">
  <div class="masthead">
    <div class="topline"><span>Vol. {issue.volume} - No. {issue.number}</span></div>
    <h1>The Daily Talk</h1>
    <div class="sub">Today's Typecheck</div>
    <div class="dateline">
      <span>{html.escape(day)}</span>
      <span>Release Edition</span>
      <span class="price">Price: {issue.price_cents}c</span>
    </div>
  </div>

  <div class="lead-head">
    <div class="kicker">{html.escape(issue.kicker)}</div>
    <h2>{html.escape(issue.headline)}</h2>
    <p class="deck">{html.escape(issue.deck)}</p>
    <div class="byline">{html.escape(issue.byline)}</div>
  </div>

  <hr class="thin">

  <div class="columns">
    {''.join(body_parts)}
  </div>

  <div class="fineprint">{html.escape(issue.footer)}</div>
</div>
</body>
</html>
'''


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a Daily Talk newspaper-style HTML release page.")
    parser.add_argument("--output", "-o", type=Path, default=None, help="Output path. Defaults to www/assets/talk/YYYY-MM-DD.html.")
    parser.add_argument("--date", type=str, default=DEFAULT_ISSUE.issue_date.isoformat(), help="Issue date in YYYY-MM-DD format.")
    args = parser.parse_args()

    issue_date = datetime.strptime(args.date, "%Y-%m-%d").date()
    issue = DEFAULT_ISSUE if issue_date == DEFAULT_ISSUE.issue_date else Issue(
        **{**DEFAULT_ISSUE.__dict__, "issue_date": issue_date, "footer": f"The Daily Talk - What's New in Talk - Release Notes for {issue_date:%B %-d, %Y}"}
    )
    output = args.output or Path("www/assets/talk") / f"{issue.issue_date.isoformat()}.html"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render_issue(issue), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
