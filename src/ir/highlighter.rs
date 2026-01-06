use crate::highlighter::{HighlightToken, Kind, render_html_with_tokens};

pub fn highlight_tokens(source: &str) -> Vec<HighlightToken> {
    let mut tokens = Vec::new();
    let bytes = source.as_bytes();
    let len = bytes.len();
    let mut i = 0usize;

    while i < len {
        let b = bytes[i];

        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }

        if b == b'/' && i + 1 < len && bytes[i + 1] == b'/' {
            let start = i;
            i += 2;
            while i < len && bytes[i] != b'\n' {
                i += 1;
            }
            push_token(&mut tokens, Kind::COMMENT, start, i);
            continue;
        }

        if b == b'%' {
            let start = i;
            i += 1;
            while i < len && is_register_char(bytes[i]) {
                i += 1;
            }
            if i > start + 1 {
                push_token(&mut tokens, Kind::PARAMETER, start, i);
            } else {
                push_token(&mut tokens, Kind::OPERATOR, start, i);
            }
            continue;
        }

        if b == b'@' {
            let start = i;
            i += 1;
            if i < len && is_ident_part(bytes[i]) {
                i += 1;
                while i < len && is_ident_part(bytes[i]) {
                    i += 1;
                }
                push_token(&mut tokens, Kind::FUNCTION, start, i);
            } else {
                push_token(&mut tokens, Kind::OPERATOR, start, i);
            }
            continue;
        }

        if b == b'#' {
            let start = i;
            i += 1;
            while i < len && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i > start + 1 {
                push_token(&mut tokens, Kind::NUMBER, start, i);
            } else {
                push_token(&mut tokens, Kind::OPERATOR, start, i);
            }
            continue;
        }

        if b == b'-' && i + 1 < len && bytes[i + 1].is_ascii_digit() {
            let start = i;
            i += 1;
            i = scan_number(bytes, i);
            push_token(&mut tokens, Kind::NUMBER, start, i);
            continue;
        }

        if b.is_ascii_digit() {
            let start = i;
            i = scan_number(bytes, i);
            push_token(&mut tokens, Kind::NUMBER, start, i);
            continue;
        }

        if is_ident_start(b) {
            let start = i;
            i += 1;
            while i < len && is_ident_part(bytes[i]) {
                i += 1;
            }
            if let Some(kind) = classify_ident(source, start, i) {
                push_token(&mut tokens, kind, start, i);
            }
            continue;
        }

        if let Some(op_len) = scan_operator(bytes, i) {
            let start = i;
            i += op_len;
            push_token(&mut tokens, Kind::OPERATOR, start, i);
            continue;
        }

        i += 1;
    }

    tokens
}

pub fn highlight_html(source: &str) -> String {
    let mut tokens = highlight_tokens(source);
    tokens.sort_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    render_html_with_tokens(source, &tokens)
}

fn push_token(tokens: &mut Vec<HighlightToken>, kind: Kind, start: usize, end: usize) {
    if end > start {
        tokens.push(HighlightToken::new(kind, start as u32, end as u32));
    }
}

fn classify_ident(source: &str, start: usize, end: usize) -> Option<Kind> {
    let ident = source.get(start..end)?;
    if is_keyword(ident) {
        return Some(Kind::KEYWORD);
    }
    if is_type(ident) {
        return Some(Kind::TYPE);
    }
    if is_literal(ident) {
        return Some(Kind::KEYWORD);
    }
    if is_meta_key(ident) {
        return Some(Kind::PROPERTY);
    }
    None
}

fn is_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "func"
            | "ret"
            | "br"
            | "jmp"
            | "phi"
            | "unreachable"
            | "const"
            | "cmp"
            | "add"
            | "sub"
            | "mul"
            | "div"
            | "ref"
            | "call"
            | "struct"
            | "record"
            | "getfield"
            | "setfield"
            | "_print"
            | "alloc"
            | "free"
            | "load"
            | "store"
            | "move"
            | "copy"
            | "gep"
            | "nominal"
    )
}

fn is_type(ident: &str) -> bool {
    matches!(
        ident,
        "int" | "float" | "bool" | "byte" | "rawptr" | "void" | "buf"
    )
}

fn is_literal(ident: &str) -> bool {
    matches!(ident, "true" | "false" | "uninit" | "poison")
}

fn is_meta_key(ident: &str) -> bool {
    matches!(ident, "id" | "recordid")
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_part(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn is_register_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'?' || b == b'_'
}

fn scan_number(bytes: &[u8], mut i: usize) -> usize {
    let len = bytes.len();
    let mut seen_dot = false;
    while i < len {
        let b = bytes[i];
        if b.is_ascii_digit() {
            i += 1;
            continue;
        }
        if b == b'.' && !seen_dot && i + 1 < len && bytes[i + 1].is_ascii_digit() {
            seen_dot = true;
            i += 1;
            continue;
        }
        break;
    }
    i
}

fn scan_operator(bytes: &[u8], i: usize) -> Option<usize> {
    let len = bytes.len();
    let b = bytes[i];
    let next = if i + 1 < len {
        Some(bytes[i + 1])
    } else {
        None
    };

    let op_len = match (b, next) {
        (b'-', Some(b'>')) => 2,
        (b'=', Some(b'=')) => 2,
        (b'!', Some(b'=')) => 2,
        (b'<', Some(b'=')) => 2,
        (b'>', Some(b'=')) => 2,
        (b'&', Some(b'&')) => 2,
        (b'|', Some(b'|')) => 2,
        (
            b'=' | b'+' | b'-' | b'*' | b'/' | b':' | b',' | b'(' | b')' | b'[' | b']' | b'{'
            | b'}' | b'<' | b'>' | b'!' | b'&' | b'|' | b'^' | b'.' | b';',
            _,
        ) => 1,
        _ => return None,
    };

    Some(op_len)
}
