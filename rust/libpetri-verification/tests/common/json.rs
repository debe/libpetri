//! Minimal JSON reader for the shared fixture file.
//!
//! The crate is deliberately dependency-free (no serde), so
//! `spec/verification-fixtures/fixtures.json` — a small, schema-stable document —
//! is read with a tiny recursive-descent parser. Test-only code: malformed JSON
//! panics with a position. Shared by the verdict-parity and script-parity runners
//! through `#[path]`.

#![allow(dead_code)]

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(entries) => entries.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    pub fn str(&self, key: &str) -> &str {
        match self.get(key) {
            Some(Json::Str(s)) => s,
            other => panic!("expected string at key '{key}', got {other:?}"),
        }
    }

    pub fn usize(&self, key: &str) -> usize {
        match self.get(key) {
            Some(Json::Num(n)) => *n as usize,
            other => panic!("expected number at key '{key}', got {other:?}"),
        }
    }

    pub fn arr(&self, key: &str) -> &[Json] {
        match self.get(key) {
            Some(Json::Arr(items)) => items,
            other => panic!("expected array at key '{key}', got {other:?}"),
        }
    }

    /// Optional string (`route`): absent -> `None`.
    pub fn str_opt(&self, key: &str) -> Option<&str> {
        match self.get(key) {
            None | Some(Json::Null) => None,
            Some(Json::Str(s)) => Some(s),
            other => panic!("expected string at key '{key}', got {other:?}"),
        }
    }

    /// Optional string array (`sinkPlaces`): absent -> empty.
    pub fn str_arr_opt(&self, key: &str) -> Vec<String> {
        match self.get(key) {
            None | Some(Json::Null) => Vec::new(),
            Some(Json::Arr(items)) => items
                .iter()
                .map(|it| match it {
                    Json::Str(s) => s.clone(),
                    other => panic!("expected string in '{key}', got {other:?}"),
                })
                .collect(),
            other => panic!("expected array at key '{key}', got {other:?}"),
        }
    }
}

pub fn parse_json(input: &str) -> Json {
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    let value = parse_value(bytes, &mut pos);
    skip_ws(bytes, &mut pos);
    assert!(pos == bytes.len(), "trailing JSON content at byte {pos}");
    value
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn expect(bytes: &[u8], pos: &mut usize, c: u8) {
    assert!(
        *pos < bytes.len() && bytes[*pos] == c,
        "expected '{}' at byte {pos:?}",
        c as char
    );
    *pos += 1;
}

fn parse_value(bytes: &[u8], pos: &mut usize) -> Json {
    skip_ws(bytes, pos);
    match bytes.get(*pos) {
        Some(b'{') => {
            *pos += 1;
            let mut entries = Vec::new();
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b'}') {
                *pos += 1;
                return Json::Obj(entries);
            }
            loop {
                skip_ws(bytes, pos);
                let key = parse_string(bytes, pos);
                skip_ws(bytes, pos);
                expect(bytes, pos, b':');
                entries.push((key, parse_value(bytes, pos)));
                skip_ws(bytes, pos);
                match bytes.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b'}') => {
                        *pos += 1;
                        return Json::Obj(entries);
                    }
                    other => panic!("expected ',' or '}}' at byte {pos:?}, got {other:?}"),
                }
            }
        }
        Some(b'[') => {
            *pos += 1;
            let mut items = Vec::new();
            skip_ws(bytes, pos);
            if bytes.get(*pos) == Some(&b']') {
                *pos += 1;
                return Json::Arr(items);
            }
            loop {
                items.push(parse_value(bytes, pos));
                skip_ws(bytes, pos);
                match bytes.get(*pos) {
                    Some(b',') => *pos += 1,
                    Some(b']') => {
                        *pos += 1;
                        return Json::Arr(items);
                    }
                    other => panic!("expected ',' or ']' at byte {pos:?}, got {other:?}"),
                }
            }
        }
        Some(b'"') => Json::Str(parse_string(bytes, pos)),
        Some(b't') => {
            assert!(bytes[*pos..].starts_with(b"true"), "bad literal at {pos:?}");
            *pos += 4;
            Json::Bool(true)
        }
        Some(b'f') => {
            assert!(bytes[*pos..].starts_with(b"false"), "bad literal at {pos:?}");
            *pos += 5;
            Json::Bool(false)
        }
        Some(b'n') => {
            assert!(bytes[*pos..].starts_with(b"null"), "bad literal at {pos:?}");
            *pos += 4;
            Json::Null
        }
        _ => {
            let start = *pos;
            while *pos < bytes.len()
                && matches!(bytes[*pos], b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E')
            {
                *pos += 1;
            }
            let text = std::str::from_utf8(&bytes[start..*pos]).unwrap();
            Json::Num(text.parse().unwrap_or_else(|_| panic!("bad number '{text}' at byte {start}")))
        }
    }
}

fn parse_string(bytes: &[u8], pos: &mut usize) -> String {
    expect(bytes, pos, b'"');
    let mut out = String::new();
    loop {
        match bytes.get(*pos) {
            Some(b'"') => {
                *pos += 1;
                return out;
            }
            Some(b'\\') => {
                *pos += 1;
                let escaped = bytes.get(*pos).copied().expect("truncated escape");
                *pos += 1;
                match escaped {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'n' => out.push('\n'),
                    b't' => out.push('\t'),
                    b'r' => out.push('\r'),
                    b'u' => {
                        let hex = std::str::from_utf8(&bytes[*pos..*pos + 4]).unwrap();
                        let code = u32::from_str_radix(hex, 16).unwrap();
                        out.push(char::from_u32(code).expect("surrogate escapes unsupported"));
                        *pos += 4;
                    }
                    other => panic!("unsupported escape '\\{}'", other as char),
                }
            }
            Some(_) => {
                // Advance one UTF-8 character.
                let rest = std::str::from_utf8(&bytes[*pos..]).unwrap();
                let c = rest.chars().next().unwrap();
                out.push(c);
                *pos += c.len_utf8();
            }
            None => panic!("unterminated string"),
        }
    }
}

