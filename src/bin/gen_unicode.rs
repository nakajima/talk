//! Generates the grapheme-cluster-break data talk's Character layer uses:
//!
//!   - `core/UnicodeData.tlk` — merged break-category table packed into a
//!     7-bit-clean string literal (interned static bytes at runtime), plus
//!     the category constants `core/Unicode.tlk` matches on.
//!   - `tests/unicode/grapheme_conformance.tlk` — the official
//!     GraphemeBreakTest cases as a self-checking talk program.
//!
//! Run manually after vendoring new UCD files under `dev/ucd/<version>/`:
//!
//!     cargo run --bin gen_unicode
//!
//! Output files are committed and reviewed like source; they carry a
//! GENERATED header.
//!
//! Encoding: the table is a sorted boundary list covering U+0000..U+10FFFF.
//! Each entry is `start_codepoint * 32 + category` (26 bits) written as
//! four big-endian base-128 septets, so every byte is <= 0x7F — valid
//! UTF-8, which a talk string literal must be. Lexicographic order equals
//! numeric order, so talk binary-searches the raw bytes directly.

use std::fmt::Write as _;

const UCD_VERSION: &str = "17.0.0";

// Category numbering shared with core/Unicode.tlk's `_GC_*` constants.
// InCB (Indic_Conjunct_Break) and Extended_Pictographic refine rather than
// cross-cut the GCB partition (asserted during generation), so one flat
// table holds all three properties.
const CAT_NAMES: &[(&str, u8)] = &[
    ("OTHER", 0),
    ("CR", 1),
    ("LF", 2),
    ("CONTROL", 3),
    ("EXTEND", 4),
    ("ZWJ", 5),
    ("REGIONAL_INDICATOR", 6),
    ("PREPEND", 7),
    ("SPACINGMARK", 8),
    ("HANGUL_L", 9),
    ("HANGUL_V", 10),
    ("HANGUL_T", 11),
    ("HANGUL_LV", 12),
    ("HANGUL_LVT", 13),
    ("EXT_PICT", 14),
    ("INCB_CONSONANT", 15),
    ("EXTEND_INCB_LINKER", 16),
    ("EXTEND_INCB_EXTEND", 17),
];

const OTHER: u8 = 0;
const CR: u8 = 1;
const LF: u8 = 2;
const CONTROL: u8 = 3;
const EXTEND: u8 = 4;
const ZWJ: u8 = 5;
const REGIONAL_INDICATOR: u8 = 6;
const PREPEND: u8 = 7;
const SPACINGMARK: u8 = 8;
const HANGUL_L: u8 = 9;
const HANGUL_V: u8 = 10;
const HANGUL_T: u8 = 11;
const HANGUL_LV: u8 = 12;
const HANGUL_LVT: u8 = 13;
const EXT_PICT: u8 = 14;
const INCB_CONSONANT: u8 = 15;
const EXTEND_INCB_LINKER: u8 = 16;
const EXTEND_INCB_EXTEND: u8 = 17;

// Character classification categories. These form a separate partition
// from grapheme-break categories; combinations preserve overlapping
// Alphabetic and Numeric properties.
const CC_OTHER: u8 = 0;
const CC_WHITESPACE: u8 = 1;
const CC_ALPHABETIC: u8 = 2;
const CC_NUMERIC: u8 = 3;
const CC_ALPHANUMERIC: u8 = 4;

const MAX_SCALAR: usize = 0x110000;

/// One parsed UCD data line: a codepoint range plus the `;`-separated
/// fields after it (property name, and for files like
/// DerivedCoreProperties a property value).
fn parse_ucd_lines(text: &str) -> Vec<(u32, u32, Vec<String>)> {
    let mut out = vec![];
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split(';').map(str::trim);
        let range = parts.next().unwrap_or("");
        let fields: Vec<String> = parts.map(str::to_string).collect();
        let (lo, hi) = match range.split_once("..") {
            Some((a, b)) => (
                u32::from_str_radix(a, 16).expect("range start"),
                u32::from_str_radix(b, 16).expect("range end"),
            ),
            None => {
                let v = u32::from_str_radix(range, 16).expect("codepoint");
                (v, v)
            }
        };
        out.push((lo, hi, fields));
    }
    out
}

fn gcb_category(name: &str) -> Option<u8> {
    Some(match name {
        "CR" => CR,
        "LF" => LF,
        "Control" => CONTROL,
        "Extend" => EXTEND,
        "ZWJ" => ZWJ,
        "Regional_Indicator" => REGIONAL_INDICATOR,
        "Prepend" => PREPEND,
        "SpacingMark" => SPACINGMARK,
        "L" => HANGUL_L,
        "V" => HANGUL_V,
        "T" => HANGUL_T,
        "LV" => HANGUL_LV,
        "LVT" => HANGUL_LVT,
        _ => return None,
    })
}

/// The per-codepoint category array: GCB assigns the base partition, then
/// Extended_Pictographic and InCB refine categories they are asserted to
/// nest inside.
fn build_categories(gcb: &str, emoji_data: &str, derived_core: &str) -> Vec<u8> {
    let mut cats = vec![OTHER; MAX_SCALAR];
    for (lo, hi, fields) in parse_ucd_lines(gcb) {
        let name = fields.first().map(String::as_str).unwrap_or("");
        let Some(cat) = gcb_category(name) else {
            panic!("unknown Grapheme_Cluster_Break value {name:?}");
        };
        for cp in lo..=hi {
            cats[cp as usize] = cat;
        }
    }
    for (lo, hi, fields) in parse_ucd_lines(emoji_data) {
        if fields.first().map(String::as_str) != Some("Extended_Pictographic") {
            continue;
        }
        for cp in lo..=hi {
            assert_eq!(
                cats[cp as usize], OTHER,
                "Extended_Pictographic U+{cp:04X} not GCB Other"
            );
            cats[cp as usize] = EXT_PICT;
        }
    }
    for (lo, hi, fields) in parse_ucd_lines(derived_core) {
        if fields.first().map(String::as_str) != Some("InCB") {
            continue;
        }
        let value = fields.get(1).map(String::as_str).unwrap_or("");
        for cp in lo..=hi {
            let cat = &mut cats[cp as usize];
            match value {
                "Consonant" => {
                    assert_eq!(*cat, OTHER, "InCB Consonant U+{cp:04X} not GCB Other");
                    *cat = INCB_CONSONANT;
                }
                "Linker" => {
                    assert_eq!(*cat, EXTEND, "InCB Linker U+{cp:04X} not GCB Extend");
                    *cat = EXTEND_INCB_LINKER;
                }
                "Extend" => {
                    // InCB Extend spans GCB Extend and ZWJ; ZWJ keeps its
                    // own category (the state machine treats it as
                    // InCB-extending for GB9c).
                    match *cat {
                        EXTEND => *cat = EXTEND_INCB_EXTEND,
                        ZWJ => {}
                        other => panic!("InCB Extend U+{cp:04X} has GCB {other}"),
                    }
                }
                _ => panic!("unknown InCB value {value:?}"),
            }
        }
    }
    cats
}

/// Compress the per-codepoint array to its category-change boundaries.
fn build_character_categories(
    derived_core: &str,
    prop_list: &str,
    general_category: &str,
) -> Vec<u8> {
    let mut alphabetic = vec![false; MAX_SCALAR];
    let mut numeric = vec![false; MAX_SCALAR];
    let mut whitespace = vec![false; MAX_SCALAR];

    for (lo, hi, fields) in parse_ucd_lines(derived_core) {
        if fields.first().map(String::as_str) == Some("Alphabetic") {
            for cp in lo..=hi {
                alphabetic[cp as usize] = true;
            }
        }
    }
    for (lo, hi, fields) in parse_ucd_lines(prop_list) {
        if fields.first().map(String::as_str) == Some("White_Space") {
            for cp in lo..=hi {
                whitespace[cp as usize] = true;
            }
        }
    }
    for (lo, hi, fields) in parse_ucd_lines(general_category) {
        if matches!(fields.first().map(String::as_str), Some("Nd" | "Nl" | "No")) {
            for cp in lo..=hi {
                numeric[cp as usize] = true;
            }
        }
    }

    (0..MAX_SCALAR)
        .map(|cp| match (whitespace[cp], alphabetic[cp], numeric[cp]) {
            (true, _, _) => CC_WHITESPACE,
            (false, true, true) => CC_ALPHANUMERIC,
            (false, true, false) => CC_ALPHABETIC,
            (false, false, true) => CC_NUMERIC,
            (false, false, false) => CC_OTHER,
        })
        .collect()
}

fn boundaries(cats: &[u8]) -> Vec<(u32, u8)> {
    let mut out = vec![];
    let mut previous = None;
    for (cp, &cat) in cats.iter().enumerate() {
        if previous != Some(cat) {
            out.push((cp as u32, cat));
            previous = Some(cat);
        }
    }
    out
}

fn encode_entry(start: u32, cat: u8) -> [u8; 4] {
    let v = (start as u64) * 32 + cat as u64;
    assert!(v < (1 << 28), "entry overflows four septets");
    [
        ((v >> 21) & 0x7F) as u8,
        ((v >> 14) & 0x7F) as u8,
        ((v >> 7) & 0x7F) as u8,
        (v & 0x7F) as u8,
    ]
}

/// A table byte as talk string-literal source text: printable ASCII stays
/// raw, everything else uses the escapes `unescape` decodes.
fn escape_byte(b: u8, out: &mut String) {
    match b {
        b'"' => out.push_str("\\\""),
        b'\\' => out.push_str("\\\\"),
        b'\n' => out.push_str("\\n"),
        b'\t' => out.push_str("\\t"),
        b'\r' => out.push_str("\\r"),
        0x20..=0x7E => out.push(b as char),
        _ => {
            let _ = write!(out, "\\u{{{b:X}}}");
        }
    }
}

fn encoded_table(entries: &[(u32, u8)]) -> String {
    let mut literal = String::new();
    for &(start, cat) in entries {
        for b in encode_entry(start, cat) {
            escape_byte(b, &mut literal);
        }
    }
    literal
}

fn render_unicode_data(gcb_entries: &[(u32, u8)], char_entries: &[(u32, u8)]) -> String {
    let gcb_literal = encoded_table(gcb_entries);
    let char_literal = encoded_table(char_entries);
    let mut out = String::new();
    // `// no-core` must stay the first line: the workspace analyzer keys
    // core-mode detection off it.
    out.push_str("// no-core\n");
    let _ = writeln!(
        out,
        "// GENERATED by gen_unicode from UCD {UCD_VERSION} - do not edit."
    );
    out.push_str(
        "// Grapheme-cluster-break categories (UAX #29), one flat partition\n\
         // merging Grapheme_Cluster_Break, Extended_Pictographic, and InCB.\n\
         // The table is a sorted boundary list: entries of four base-128\n\
         // septets encoding start_codepoint * 32 + category. See\n\
         // src/bin/gen_unicode.rs for the encoding and regeneration story.\n\
         use package::String::{ String }\n\n",
    );
    for (name, value) in CAT_NAMES {
        let _ = writeln!(out, "public let _GC_{name}: Int = {value}");
    }
    let _ = writeln!(
        out,
        "\npublic func _gcb_table() -> String {{\n\t\"{gcb_literal}\"\n}}"
    );
    out.push_str(
        "\npublic let _CC_OTHER: Int = 0\n\
         public let _CC_WHITESPACE: Int = 1\n\
         public let _CC_ALPHABETIC: Int = 2\n\
         public let _CC_NUMERIC: Int = 3\n\
         public let _CC_ALPHANUMERIC: Int = 4\n",
    );
    let _ = writeln!(
        out,
        "\npublic func _character_class_table() -> String {{\n\t\"{char_literal}\"\n}}"
    );
    out
}

/// The official GraphemeBreakTest cases as one self-checking talk program:
/// for each case the iterator's per-cluster byte counts (joined with `,`)
/// must equal the expected spelling.
fn render_conformance(test_text: &str) -> (String, usize) {
    let mut body = String::new();
    let mut cases: Vec<String> = vec![];
    let mut count = 0;
    for line in test_text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        // ÷ 0020 × 0308 ÷ 0020 ÷  — scalars separated by break (÷) or
        // no-break (×) marks, with marks at both ends.
        let mut scalars: Vec<u32> = vec![];
        let mut breaks_after: Vec<bool> = vec![];
        for token in line.split_whitespace() {
            match token {
                "÷" | "×" => {
                    if !scalars.is_empty() {
                        breaks_after.push(token == "÷");
                    }
                }
                hex => {
                    scalars.push(u32::from_str_radix(hex, 16).expect("test scalar"));
                }
            }
        }
        if scalars.is_empty() {
            continue;
        }
        assert_eq!(
            breaks_after.len(),
            scalars.len(),
            "malformed test line: {line}"
        );
        let mut literal = String::new();
        let mut cluster_lens: Vec<usize> = vec![];
        let mut current = 0usize;
        for (scalar, &breaks) in scalars.iter().zip(&breaks_after) {
            let ch = char::from_u32(*scalar).expect("test scalars are valid");
            let _ = write!(literal, "\\u{{{scalar:X}}}");
            current += ch.len_utf8();
            if breaks {
                cluster_lens.push(current);
                current = 0;
            }
        }
        let expected: String = cluster_lens.iter().map(|len| format!("{len},")).collect();
        count += 1;
        cases.push(format!("check(\"{literal}\", \"{expected}\", {count})"));
    }
    // Batch the cases into functions: the reference evaluator recurses
    // per sequential statement, and a single 766-statement block
    // overflows its stack.
    const BATCH: usize = 64;
    let mut calls = String::new();
    for (index, batch) in cases.chunks(BATCH).enumerate() {
        let _ = writeln!(body, "func run_batch_{index}() -> () {{");
        for case in batch {
            let _ = writeln!(body, "\t{case}");
        }
        let _ = writeln!(body, "}}\n");
        let _ = writeln!(calls, "run_batch_{index}()");
    }
    body.push_str(&calls);
    let mut out = String::new();
    let _ = writeln!(
        out,
        "// GENERATED by gen_unicode from GraphemeBreakTest-{UCD_VERSION}.txt — do not edit."
    );
    out.push_str(
        "let failures = 0\n\
         let total = 0\n\n\
         func check(s: String, expected: String, case_number: Int) -> () {\n\
         \ttotal = total + 1\n\
         \tlet lens = \"\"\n\
         \tfor ch in s {\n\
         \t\tlens = lens + ch.utf8_count().show() + \",\"\n\
         \t}\n\
         \t// Compare through borrows: String == consumes its operands,\n\
         \t// which the failure report below still needs.\n\
         \tif lens.as_substring().equals_string(expected) {\n\
         \t\treturn ()\n\
         \t}\n\
         \tfailures = failures + 1\n\
         \tprint(\"case \" + case_number.show() + \": got \" + lens + \" want \" + expected)\n\
         }\n\n",
    );
    out.push_str(&body);
    let _ = write!(
        out,
        "\nprint(\"failures: \" + failures.show() + \" / \" + total.show())\n"
    );
    (out, count)
}

fn main() {
    let dir = format!("dev/ucd/{UCD_VERSION}");
    let read = |name: &str| {
        std::fs::read_to_string(format!("{dir}/{name}"))
            .unwrap_or_else(|e| panic!("reading {dir}/{name}: {e} — vendor the UCD files first"))
    };
    let cats = build_categories(
        &read("GraphemeBreakProperty.txt"),
        &read("emoji-data.txt"),
        &read("DerivedCoreProperties.txt"),
    );
    let entries = boundaries(&cats);
    let char_cats = build_character_categories(
        &read("DerivedCoreProperties.txt"),
        &read("PropList.txt"),
        &read("DerivedGeneralCategory.txt"),
    );
    let char_entries = boundaries(&char_cats);
    let data = render_unicode_data(&entries, &char_entries);
    std::fs::write("core/UnicodeData.tlk", &data).expect("writing core/UnicodeData.tlk");
    let (conformance, cases) = render_conformance(&read("GraphemeBreakTest.txt"));
    std::fs::create_dir_all("tests/unicode").expect("creating tests/unicode");
    std::fs::write("tests/unicode/grapheme_conformance.tlk", conformance)
        .expect("writing conformance program");
    println!(
        "wrote core/UnicodeData.tlk ({} grapheme entries, {} character-class entries) and \
         tests/unicode/grapheme_conformance.tlk ({cases} cases)",
        entries.len(),
        char_entries.len(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    const GCB_FIXTURE: &str = "\
# Comment line
000D          ; CR # Cc <control-000D>
000A          ; LF
0000..0009    ; Control
0300..0301    ; Extend
200D          ; ZWJ
094D          ; Extend
0915..0916    ; Other-Is-Not-Emitted
";

    #[test]
    fn parses_ranges_and_singletons() {
        let lines = parse_ucd_lines(GCB_FIXTURE);
        assert_eq!(lines[0], (0x0D, 0x0D, vec!["CR".to_string()]));
        assert_eq!(lines[2], (0x0000, 0x0009, vec!["Control".to_string()]));
    }

    #[test]
    fn merges_incb_and_extpict_into_gcb() {
        let gcb = "\
000D ; CR
0300..0301 ; Extend
094D ; Extend
200D ; ZWJ
";
        let emoji = "\
1F600..1F601 ; Extended_Pictographic
0041 ; Some_Other_Emoji_Property
";
        let derived = "\
0915..0916 ; InCB; Consonant
094D ; InCB; Linker
0300 ; InCB; Extend
200D ; InCB; Extend
0041 ; Math
";
        let cats = build_categories(gcb, emoji, derived);
        assert_eq!(cats[0x0D], CR);
        assert_eq!(cats[0x0300], EXTEND_INCB_EXTEND);
        assert_eq!(cats[0x0301], EXTEND);
        assert_eq!(cats[0x094D], EXTEND_INCB_LINKER);
        assert_eq!(cats[0x0915], INCB_CONSONANT);
        assert_eq!(cats[0x200D], ZWJ);
        assert_eq!(cats[0x1F600], EXT_PICT);
        assert_eq!(cats[0x0041], OTHER);
    }

    #[test]
    fn boundary_list_compresses_runs() {
        let mut cats = vec![OTHER; 16];
        cats[4..8].fill(EXTEND);
        assert_eq!(boundaries(&cats), vec![(0, OTHER), (4, EXTEND), (8, OTHER)]);
    }

    #[test]
    fn septet_encoding_is_seven_bit_and_ordered() {
        let low = encode_entry(0, CR);
        let high = encode_entry(0x10FFFF, EXTEND_INCB_EXTEND);
        for b in low.iter().chain(high.iter()) {
            assert!(*b <= 0x7F);
        }
        // Lexicographic byte order must equal numeric codepoint order.
        assert!(low < high);
        let mid = encode_entry(0x0916, INCB_CONSONANT);
        assert!(low < mid && mid < high);
        // Decode round-trip.
        let v = mid.iter().fold(0u64, |acc, &b| acc * 128 + b as u64);
        assert_eq!(v / 32, 0x0916);
        assert_eq!(v % 32, INCB_CONSONANT as u64);
    }

    #[test]
    fn escaped_bytes_stay_seven_bit_clean_through_unescape() {
        let mut literal = String::new();
        for b in 0u8..=0x7F {
            escape_byte(b, &mut literal);
        }
        let decoded = talk::parsing::lexing::unescape(&literal).expect("valid escapes");
        let bytes: Vec<u8> = decoded.into_bytes();
        assert_eq!(bytes, (0u8..=0x7F).collect::<Vec<u8>>());
    }

    #[test]
    fn conformance_renderer_computes_cluster_byte_lengths() {
        // ÷ 0061 × 0301 ÷ 1F600 ÷  — "a" + combining acute is one 3-byte
        // cluster, the emoji a 4-byte cluster.
        let (program, cases) =
            render_conformance("÷ 0061 × 0301 ÷ 1F600 ÷ # a\u{301} then emoji\n");
        assert_eq!(cases, 1);
        assert!(program.contains("check(\"\\u{61}\\u{301}\\u{1F600}\", \"3,4,\", 1)"));
    }
}
