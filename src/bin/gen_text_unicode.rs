//! Generates Unicode 17 text-property, case-mapping, and normalization data.
//!
//! Run after vendoring the pinned UCD files under `dev/ucd/17.0.0`:
//!
//!     cargo run --bin gen_text_unicode
//!
//! The generated Talk module stores lookup indices as fixed-width base-128
//! septets and mapping payloads as ordinary UTF-8 string literals.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    fs,
};

const UCD_VERSION: &str = "17.0.0";
const MAX_SCALAR: usize = 0x110000;

const LOWERCASE: u16 = 1;
const UPPERCASE: u16 = 2;
const TITLECASE: u16 = 4;
const DECIMAL: u16 = 8;
const DIGIT: u16 = 16;
const PUNCTUATION: u16 = 32;
const SYMBOL: u16 = 64;
const CONTROL: u16 = 128;
const PRINTABLE: u16 = 256;
const CASED: u16 = 512;
const CASE_IGNORABLE: u16 = 1024;

#[derive(Clone)]
struct Record {
    scalar: u32,
    combining_class: u8,
    decomposition: Vec<u32>,
    compatibility: bool,
    decimal: bool,
    digit: bool,
    uppercase: Vec<u32>,
    lowercase: Vec<u32>,
    titlecase: Vec<u32>,
}

struct Ucd {
    records: Vec<Record>,
    derived_core: String,
    general_categories: String,
    special_casing: String,
    case_folding: String,
    normalization_properties: String,
    #[cfg(test)]
    normalization_test: String,
    word_break: String,
    #[cfg(test)]
    word_break_test: String,
    #[cfg(test)]
    emoji_data: String,
}

impl Ucd {
    fn read() -> Self {
        let dir = format!("dev/ucd/{UCD_VERSION}");
        let read = |name: &str| {
            fs::read_to_string(format!("{dir}/{name}"))
                .unwrap_or_else(|error| panic!("reading {dir}/{name}: {error}"))
        };
        Self {
            records: Self::parse_unicode_data(&read("UnicodeData.txt")),
            derived_core: read("DerivedCoreProperties.txt"),
            general_categories: read("DerivedGeneralCategory.txt"),
            special_casing: read("SpecialCasing.txt"),
            case_folding: read("CaseFolding.txt"),
            normalization_properties: read("DerivedNormalizationProps.txt"),
            #[cfg(test)]
            normalization_test: read("NormalizationTest.txt"),
            word_break: read("WordBreakProperty.txt"),
            #[cfg(test)]
            word_break_test: read("WordBreakTest.txt"),
            #[cfg(test)]
            emoji_data: read("emoji-data.txt"),
        }
    }

    fn parse_hex_sequence(field: &str) -> Vec<u32> {
        field
            .split_whitespace()
            .map(|value| u32::from_str_radix(value, 16).expect("hex scalar"))
            .collect()
    }

    fn parse_unicode_data(text: &str) -> Vec<Record> {
        text.lines()
            .filter(|line| !line.is_empty())
            .map(|line| {
                let fields: Vec<&str> = line.split(';').collect();
                assert!(fields.len() >= 15, "malformed UnicodeData line: {line}");
                let raw_decomposition = fields[5].trim();
                let compatibility = raw_decomposition.starts_with('<');
                let decomposition = Self::parse_hex_sequence(
                    raw_decomposition
                        .split_once('>')
                        .map_or(raw_decomposition, |(_, rest)| rest),
                );
                Record {
                    scalar: u32::from_str_radix(fields[0], 16).expect("scalar"),
                    combining_class: fields[3].parse().expect("combining class"),
                    decomposition,
                    compatibility,
                    decimal: !fields[6].is_empty(),
                    digit: !fields[7].is_empty() || !fields[6].is_empty(),
                    uppercase: Self::parse_hex_sequence(fields[12]),
                    lowercase: Self::parse_hex_sequence(fields[13]),
                    titlecase: Self::parse_hex_sequence(fields[14]),
                }
            })
            .collect()
    }

    fn property_lines(text: &str) -> impl Iterator<Item = (u32, u32, &str, Option<&str>)> {
        text.lines().filter_map(|line| {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                return None;
            }
            let mut fields = line.split(';').map(str::trim);
            let range = fields.next()?;
            let property = fields.next()?;
            let value = fields.next();
            let (start, end) = range.split_once("..").map_or_else(
                || {
                    let scalar = u32::from_str_radix(range, 16).expect("property scalar");
                    (scalar, scalar)
                },
                |(start, end)| {
                    (
                        u32::from_str_radix(start, 16).expect("property start"),
                        u32::from_str_radix(end, 16).expect("property end"),
                    )
                },
            );
            Some((start, end, property, value))
        })
    }

    fn property_flags(&self) -> Vec<u16> {
        let mut flags = vec![0u16; MAX_SCALAR];
        for (start, end, property, _) in Self::property_lines(&self.derived_core) {
            let bit = match property {
                "Lowercase" => LOWERCASE,
                "Uppercase" => UPPERCASE,
                "Cased" => CASED,
                "Case_Ignorable" => CASE_IGNORABLE,
                _ => continue,
            };
            for scalar in start..=end {
                flags[scalar as usize] |= bit;
            }
        }
        for (start, end, category, _) in Self::property_lines(&self.general_categories) {
            let bit = match category {
                "Lt" => TITLECASE,
                "Nd" => DECIMAL | DIGIT,
                value if value.starts_with('P') => PUNCTUATION,
                value if value.starts_with('S') => SYMBOL,
                "Cc" => CONTROL,
                _ => 0,
            };
            let printable = !matches!(
                category,
                "Cc" | "Cf" | "Cs" | "Co" | "Cn" | "Zl" | "Zp" | "Zs"
            );
            for scalar in start..=end {
                flags[scalar as usize] |= bit;
                if printable || scalar == 0x20 {
                    flags[scalar as usize] |= PRINTABLE;
                }
            }
        }
        for record in &self.records {
            if record.decimal {
                flags[record.scalar as usize] |= DECIMAL | DIGIT;
            } else if record.digit {
                flags[record.scalar as usize] |= DIGIT;
            }
        }
        flags
    }

    fn case_maps(&self) -> [BTreeMap<u32, Vec<u32>>; 4] {
        let mut lowercase = BTreeMap::new();
        let mut uppercase = BTreeMap::new();
        let mut titlecase = BTreeMap::new();
        for record in &self.records {
            if !record.lowercase.is_empty() {
                lowercase.insert(record.scalar, record.lowercase.clone());
            }
            if !record.uppercase.is_empty() {
                uppercase.insert(record.scalar, record.uppercase.clone());
            }
            if !record.titlecase.is_empty() {
                titlecase.insert(record.scalar, record.titlecase.clone());
            }
        }
        for line in self.special_casing.lines() {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let fields: Vec<&str> = line.split(';').map(str::trim).collect();
            if fields.len() < 4 || fields.get(4).is_some_and(|condition| !condition.is_empty()) {
                continue;
            }
            let scalar = u32::from_str_radix(fields[0], 16).expect("special casing scalar");
            lowercase.insert(scalar, Self::parse_hex_sequence(fields[1]));
            titlecase.insert(scalar, Self::parse_hex_sequence(fields[2]));
            uppercase.insert(scalar, Self::parse_hex_sequence(fields[3]));
        }
        let mut folding = BTreeMap::new();
        for line in self.case_folding.lines() {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let fields: Vec<&str> = line.split(';').map(str::trim).collect();
            if fields.len() < 3 || !matches!(fields[1], "C" | "F") {
                continue;
            }
            folding.insert(
                u32::from_str_radix(fields[0], 16).expect("case fold scalar"),
                Self::parse_hex_sequence(fields[2]),
            );
        }
        [lowercase, uppercase, titlecase, folding]
    }

    fn word_categories(&self) -> Vec<u8> {
        let mut categories = vec![0u8; MAX_SCALAR];
        for (start, end, property, _) in Self::property_lines(&self.word_break) {
            let category = match property {
                "CR" => 1,
                "LF" => 2,
                "Newline" => 3,
                "Extend" => 4,
                "ZWJ" => 5,
                "Regional_Indicator" => 6,
                "Format" => 7,
                "Katakana" => 8,
                "Hebrew_Letter" => 9,
                "ALetter" => 10,
                "Single_Quote" => 11,
                "Double_Quote" => 12,
                "MidNumLet" => 13,
                "MidLetter" => 14,
                "MidNum" => 15,
                "Numeric" => 16,
                "ExtendNumLet" => 17,
                "WSegSpace" => 18,
                _ => continue,
            };
            for scalar in start..=end {
                categories[scalar as usize] = category;
            }
        }
        categories
    }

    fn normalization_maps(
        &self,
    ) -> (
        BTreeMap<u32, Vec<u32>>,
        BTreeMap<u32, Vec<u32>>,
        Vec<u8>,
        BTreeMap<(u32, u32), u32>,
    ) {
        let mut canonical = BTreeMap::new();
        let mut compatibility = BTreeMap::new();
        let mut combining = vec![0u8; MAX_SCALAR];
        for record in &self.records {
            combining[record.scalar as usize] = record.combining_class;
            if !record.decomposition.is_empty() {
                compatibility.insert(record.scalar, record.decomposition.clone());
                if !record.compatibility {
                    canonical.insert(record.scalar, record.decomposition.clone());
                }
            }
        }
        let mut exclusions = BTreeSet::new();
        for (start, end, property, _) in Self::property_lines(&self.normalization_properties) {
            if property == "Full_Composition_Exclusion" {
                exclusions.extend(start..=end);
            }
        }
        let mut composition = BTreeMap::new();
        for (&scalar, mapping) in &canonical {
            if mapping.len() == 2 && !exclusions.contains(&scalar) {
                composition.insert((mapping[0], mapping[1]), scalar);
            }
        }
        (canonical, compatibility, combining, composition)
    }
}

#[cfg(test)]
struct WordBreaker {
    categories: Vec<u8>,
    extended_pictographic: Vec<bool>,
}

#[cfg(test)]
impl WordBreaker {
    fn from_ucd(ucd: &Ucd) -> Self {
        let mut extended_pictographic = vec![false; MAX_SCALAR];
        for (start, end, property, _) in Ucd::property_lines(&ucd.emoji_data) {
            if property == "Extended_Pictographic" {
                for scalar in start..=end {
                    extended_pictographic[scalar as usize] = true;
                }
            }
        }
        Self {
            categories: ucd.word_categories(),
            extended_pictographic,
        }
    }

    fn ignored(category: u8) -> bool {
        matches!(category, 4 | 5 | 7)
    }

    fn ah(category: u8) -> bool {
        matches!(category, 9 | 10)
    }

    fn mid_letter(category: u8) -> bool {
        matches!(category, 11 | 13 | 14)
    }

    fn mid_number(category: u8) -> bool {
        matches!(category, 11 | 13 | 15)
    }

    fn previous(categories: &[u8], before: usize) -> Option<usize> {
        (0..before)
            .rev()
            .find(|index| !Self::ignored(categories[*index]))
    }

    fn next(categories: &[u8], from: usize) -> Option<usize> {
        (from..categories.len()).find(|index| !Self::ignored(categories[*index]))
    }

    fn breaks(&self, scalars: &[u32], index: usize) -> bool {
        let categories: Vec<u8> = scalars
            .iter()
            .map(|scalar| self.categories[*scalar as usize])
            .collect();
        let immediate_left = categories[index - 1];
        let immediate_right = categories[index];
        if immediate_left == 1 && immediate_right == 2 {
            return false;
        }
        if matches!(immediate_left, 1 | 2 | 3) || matches!(immediate_right, 1 | 2 | 3) {
            return true;
        }
        if immediate_left == 18 && immediate_right == 18 {
            return false;
        }
        if Self::ignored(immediate_right) {
            return false;
        }
        if immediate_left == 5 && self.extended_pictographic[scalars[index] as usize] {
            return false;
        }
        let Some(left_index) = Self::previous(&categories, index) else {
            return true;
        };
        let left = categories[left_index];
        let right = immediate_right;
        if left == 5 && self.extended_pictographic[scalars[index] as usize] {
            return false;
        }
        if Self::ah(left) && Self::ah(right) {
            return false;
        }
        if Self::ah(left)
            && Self::mid_letter(right)
            && Self::next(&categories, index + 1).is_some_and(|next| Self::ah(categories[next]))
        {
            return false;
        }
        if Self::mid_letter(left)
            && Self::ah(right)
            && Self::previous(&categories, left_index)
                .is_some_and(|previous| Self::ah(categories[previous]))
        {
            return false;
        }
        if left == 9 && right == 11 {
            return false;
        }
        if left == 9
            && right == 12
            && Self::next(&categories, index + 1).is_some_and(|next| categories[next] == 9)
        {
            return false;
        }
        if left == 12
            && right == 9
            && Self::previous(&categories, left_index)
                .is_some_and(|previous| categories[previous] == 9)
        {
            return false;
        }
        if (left == 16 && right == 16)
            || (Self::ah(left) && right == 16)
            || (left == 16 && Self::ah(right))
        {
            return false;
        }
        if left == 16
            && Self::mid_number(right)
            && Self::next(&categories, index + 1).is_some_and(|next| categories[next] == 16)
        {
            return false;
        }
        if Self::mid_number(left)
            && right == 16
            && Self::previous(&categories, left_index)
                .is_some_and(|previous| categories[previous] == 16)
        {
            return false;
        }
        if left == 8 && right == 8 {
            return false;
        }
        if (Self::ah(left) || matches!(left, 8 | 16 | 17)) && right == 17 {
            return false;
        }
        if left == 17 && (Self::ah(right) || matches!(right, 8 | 16)) {
            return false;
        }
        if left == 6 && right == 6 {
            let mut run = 0;
            let mut position = Some(left_index);
            while let Some(index) = position {
                if categories[index] != 6 {
                    break;
                }
                run += 1;
                position = Self::previous(&categories, index);
            }
            if run % 2 == 1 {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
struct Normalizer {
    canonical: BTreeMap<u32, Vec<u32>>,
    compatibility: BTreeMap<u32, Vec<u32>>,
    combining: Vec<u8>,
    composition: BTreeMap<(u32, u32), u32>,
}

#[cfg(test)]
impl Normalizer {
    fn from_ucd(ucd: &Ucd) -> Self {
        let (canonical, compatibility, combining, composition) = ucd.normalization_maps();
        Self {
            canonical,
            compatibility,
            combining,
            composition,
        }
    }

    fn decompose_scalar(&self, scalar: u32, compatibility: bool, output: &mut Vec<u32>) {
        let syllable = scalar.wrapping_sub(0xac00);
        if syllable < 11172 {
            output.push(0x1100 + syllable / 588);
            output.push(0x1161 + (syllable % 588) / 28);
            if syllable % 28 != 0 {
                output.push(0x11a7 + syllable % 28);
            }
            return;
        }
        let mapping = if compatibility {
            self.compatibility.get(&scalar)
        } else {
            self.canonical.get(&scalar)
        };
        if let Some(mapping) = mapping {
            for &component in mapping {
                self.decompose_scalar(component, compatibility, output);
            }
        } else {
            output.push(scalar);
        }
    }

    fn decompose(&self, input: &[u32], compatibility: bool) -> Vec<u32> {
        let mut output = Vec::new();
        for &scalar in input {
            self.decompose_scalar(scalar, compatibility, &mut output);
        }
        for index in 1..output.len() {
            let class = self.combining[output[index] as usize];
            let mut position = index;
            while position > 0 && class != 0 {
                let previous = self.combining[output[position - 1] as usize];
                if previous == 0 || previous <= class {
                    break;
                }
                output.swap(position - 1, position);
                position -= 1;
            }
        }
        output
    }

    fn hangul_composition(starter: u32, next: u32) -> Option<u32> {
        let leading = starter.wrapping_sub(0x1100);
        let vowel = next.wrapping_sub(0x1161);
        if leading < 19 && vowel < 21 {
            return Some(0xac00 + (leading * 21 + vowel) * 28);
        }
        let syllable = starter.wrapping_sub(0xac00);
        let trailing = next.wrapping_sub(0x11a7);
        if syllable < 11172 && syllable % 28 == 0 && trailing > 0 && trailing < 28 {
            Some(starter + trailing)
        } else {
            None
        }
    }

    fn compose(&self, input: &[u32]) -> Vec<u32> {
        let Some(&first) = input.first() else {
            return Vec::new();
        };
        let mut output = vec![first];
        let mut starter_position = 0;
        let mut starter = first;
        let mut previous_class = 0;
        for &scalar in &input[1..] {
            let class = self.combining[scalar as usize];
            let composite = Self::hangul_composition(starter, scalar)
                .or_else(|| self.composition.get(&(starter, scalar)).copied());
            if let Some(composite) = composite
                && (previous_class == 0 || previous_class < class)
            {
                output[starter_position] = composite;
                starter = composite;
            } else {
                if class == 0 {
                    starter_position = output.len();
                    starter = scalar;
                }
                output.push(scalar);
                previous_class = class;
            }
        }
        output
    }

    fn normalize(&self, input: &[u32], compatibility: bool, compose: bool) -> Vec<u32> {
        let decomposed = self.decompose(input, compatibility);
        if compose {
            self.compose(&decomposed)
        } else {
            decomposed
        }
    }
}

struct Renderer {
    output: String,
}

impl Renderer {
    fn new() -> Self {
        Self {
            output: format!(
                "// no-core\n// GENERATED by gen_text_unicode from UCD {UCD_VERSION} - do not edit.\nuse package::String::{{ String }}\n\n"
            ),
        }
    }

    fn septets(mut value: u64, width: usize) -> Vec<u8> {
        let mut bytes = vec![0; width];
        for byte in bytes.iter_mut().rev() {
            *byte = (value & 0x7f) as u8;
            value >>= 7;
        }
        assert_eq!(value, 0, "value does not fit in {width} septets");
        bytes
    }

    fn escape_bytes(bytes: &[u8]) -> String {
        let mut output = String::new();
        for &byte in bytes {
            match byte {
                b'"' => output.push_str("\\\""),
                b'\\' => output.push_str("\\\\"),
                b'\n' => output.push_str("\\n"),
                b'\r' => output.push_str("\\r"),
                b'\t' => output.push_str("\\t"),
                0x20..=0x7e => output.push(byte as char),
                _ => write!(output, "\\u{{{byte:X}}}").expect("write escape"),
            }
        }
        output
    }

    fn escape_text(text: &str) -> String {
        let mut output = String::new();
        for character in text.chars() {
            match character {
                '"' => output.push_str("\\\""),
                '\\' => output.push_str("\\\\"),
                '\n' => output.push_str("\\n"),
                '\r' => output.push_str("\\r"),
                '\t' => output.push_str("\\t"),
                value if value.is_ascii_graphic() || value == ' ' => output.push(value),
                value => write!(output, "\\u{{{:X}}}", value as u32).expect("write scalar"),
            }
        }
        output
    }

    fn boundaries<T: Copy + Eq>(values: &[T]) -> Vec<(u32, T)> {
        let mut output = Vec::new();
        let mut previous = None;
        for (scalar, &value) in values.iter().enumerate() {
            if previous != Some(value) {
                output.push((scalar as u32, value));
                previous = Some(value);
            }
        }
        output
    }

    fn table(&mut self, name: &str, bytes: &[u8]) {
        let literal = Self::escape_bytes(bytes);
        writeln!(
            self.output,
            "pub func {name}() -> String {{\n\t\"{literal}\"\n}}\n"
        )
        .expect("write table");
    }

    fn boundary_table(&mut self, name: &str, values: &[u16], radix: u64, width: usize) {
        let mut bytes = Vec::new();
        for (scalar, value) in Self::boundaries(values) {
            bytes.extend(Self::septets(scalar as u64 * radix + value as u64, width));
        }
        self.table(name, &bytes);
    }

    fn byte_boundary_table(&mut self, name: &str, values: &[u8], radix: u64, width: usize) {
        let widened: Vec<u16> = values.iter().map(|value| *value as u16).collect();
        self.boundary_table(name, &widened, radix, width);
    }

    fn mapping_table(&mut self, name: &str, mappings: &BTreeMap<u32, Vec<u32>>) {
        let mut index = Vec::new();
        let mut payload = String::new();
        for (&scalar, mapping) in mappings {
            let offset = payload.len();
            for &mapped in mapping {
                payload.push(char::from_u32(mapped).expect("valid mapping scalar"));
            }
            let length = payload.len() - offset;
            index.extend(Self::septets(scalar as u64, 3));
            index.extend(Self::septets(offset as u64, 3));
            index.extend(Self::septets(length as u64, 1));
        }
        self.table(&format!("_{name}_index"), &index);
        let literal = Self::escape_text(&payload);
        writeln!(
            self.output,
            "pub func _{name}_payload() -> String {{\n\t\"{literal}\"\n}}\n"
        )
        .expect("write payload");
    }

    fn composition_table(&mut self, mappings: &BTreeMap<(u32, u32), u32>) {
        let mut bytes = Vec::new();
        for (&(starter, combining), &result) in mappings {
            bytes.extend(Self::septets(starter as u64, 3));
            bytes.extend(Self::septets(combining as u64, 3));
            bytes.extend(Self::septets(result as u64, 3));
        }
        self.table("_composition_table", &bytes);
    }

    fn finish(mut self, ucd: &Ucd) -> String {
        self.boundary_table("_text_property_table", &ucd.property_flags(), 4096, 5);
        self.byte_boundary_table("_word_break_table", &ucd.word_categories(), 32, 4);
        let [lower, upper, title, fold] = ucd.case_maps();
        self.mapping_table("lowercase", &lower);
        self.mapping_table("uppercase", &upper);
        self.mapping_table("titlecase", &title);
        self.mapping_table("casefold", &fold);
        let (canonical, compatibility, combining, composition) = ucd.normalization_maps();
        self.mapping_table("canonical_decomposition", &canonical);
        self.mapping_table("compatibility_decomposition", &compatibility);
        self.byte_boundary_table("_combining_class_table", &combining, 256, 5);
        self.composition_table(&composition);
        self.output.pop();
        self.output
    }
}

fn main() {
    let ucd = Ucd::read();
    let generated = Renderer::new().finish(&ucd);
    fs::write("core/TextUnicodeData.tlk", generated).expect("write TextUnicodeData.tlk");
    println!("wrote core/TextUnicodeData.tlk from Unicode {UCD_VERSION}");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_tables_include_expanding_case_and_normalization_entries() {
        let ucd = Ucd::read();
        let [lower, upper, _, fold] = ucd.case_maps();
        assert_eq!(upper.get(&0x00df), Some(&vec![0x53, 0x53]));
        assert_eq!(lower.get(&0x0130), Some(&vec![0x69, 0x0307]));
        assert_eq!(fold.get(&0x00df), Some(&vec![0x73, 0x73]));
        let (canonical, compatibility, _, composition) = ucd.normalization_maps();
        assert_eq!(canonical.get(&0x00e9), Some(&vec![0x65, 0x0301]));
        assert_eq!(compatibility.get(&0xfb01), Some(&vec![0x66, 0x69]));
        assert_eq!(composition.get(&(0x65, 0x0301)), Some(&0x00e9));
    }

    #[test]
    fn word_breaks_match_the_official_unicode_suite() {
        let ucd = Ucd::read();
        let breaker = WordBreaker::from_ucd(&ucd);
        let mut cases = 0;
        for line in ucd.word_break_test.lines() {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let mut scalars = Vec::new();
            let mut expected = Vec::new();
            let mut next_break = true;
            for token in line.split_whitespace() {
                match token {
                    "÷" => next_break = true,
                    "×" => next_break = false,
                    scalar => {
                        if !scalars.is_empty() {
                            expected.push(next_break);
                        }
                        scalars.push(u32::from_str_radix(scalar, 16).expect("word scalar"));
                    }
                }
            }
            for index in 1..scalars.len() {
                assert_eq!(
                    breaker.breaks(&scalars, index),
                    expected[index - 1],
                    "{line}"
                );
            }
            cases += 1;
        }
        assert!(cases > 1_000, "expected the complete word-break suite");
    }

    #[test]
    fn normalization_matches_the_official_unicode_suite() {
        let ucd = Ucd::read();
        let normalizer = Normalizer::from_ucd(&ucd);
        let mut cases = 0;
        for line in ucd.normalization_test.lines() {
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() || line.starts_with('@') {
                continue;
            }
            let columns: Vec<Vec<u32>> = line
                .split(';')
                .take(5)
                .map(|column| Ucd::parse_hex_sequence(column.trim()))
                .collect();
            assert_eq!(columns.len(), 5, "malformed normalization case: {line}");
            let [source, nfc, nfd, nfkc, nfkd] = columns.as_slice() else {
                unreachable!()
            };
            for input in [source, nfc, nfd] {
                assert_eq!(
                    normalizer.normalize(input, false, true),
                    *nfc,
                    "NFC: {line}"
                );
                assert_eq!(
                    normalizer.normalize(input, false, false),
                    *nfd,
                    "NFD: {line}"
                );
            }
            for input in [nfkc, nfkd] {
                assert_eq!(
                    normalizer.normalize(input, false, true),
                    *nfkc,
                    "NFC(K): {line}"
                );
                assert_eq!(
                    normalizer.normalize(input, false, false),
                    *nfkd,
                    "NFD(K): {line}"
                );
            }
            for input in [source, nfc, nfd, nfkc, nfkd] {
                assert_eq!(
                    normalizer.normalize(input, true, true),
                    *nfkc,
                    "NFKC: {line}"
                );
                assert_eq!(
                    normalizer.normalize(input, true, false),
                    *nfkd,
                    "NFKD: {line}"
                );
            }
            cases += 1;
        }
        assert!(cases > 10_000, "expected the complete normalization suite");
    }

    #[test]
    fn fixed_width_septets_round_trip() {
        for (value, width) in [(0, 1), (0x10ffff, 3), (u32::MAX as u64, 5)] {
            let encoded = Renderer::septets(value, width);
            assert!(encoded.iter().all(|byte| *byte < 128));
            let decoded = encoded
                .iter()
                .fold(0u64, |accumulator, byte| accumulator * 128 + *byte as u64);
            assert_eq!(decoded, value);
        }
    }
}
