//! Label patterns in Metamath range syntax.
//!
//! A pattern is a comma-separated list of items. Each item is either a glob,
//! where `*` matches any sequence of characters and `?` matches any single
//! character, or a range `a~b`, which
//! matches every statement from `a` to `b` inclusive in database order. Either
//! endpoint of a range may be omitted to mean the start or end of the database.

/// A parsed label pattern.
#[derive(Debug, Clone, Default)]
pub struct Pattern {
    items: Vec<Item>,
}

#[derive(Debug, Clone)]
enum Item {
    Glob(Vec<u8>),
    Range(Option<u32>, Option<u32>),
}

impl Pattern {
    /// Parses a pattern. `resolve` maps a label to its position in the
    /// database, and is used for the endpoints of ranges.
    pub fn parse(s: &str, resolve: impl Fn(&[u8]) -> Option<u32>) -> Result<Pattern, String> {
        let mut items = Vec::new();
        for item in s.split(',') {
            let item = item.trim();
            if item.is_empty() {
                return Err(format!("empty item in pattern '{s}'"));
            }
            if let Some((start, end)) = item.split_once('~') {
                let endpoint = |label: &str| -> Result<Option<u32>, String> {
                    if label.is_empty() {
                        return Ok(None);
                    }
                    if label.contains(['*', '?', '~']) {
                        return Err(format!("invalid range endpoint '{label}' in pattern '{s}'"));
                    }
                    resolve(label.as_bytes())
                        .map(Some)
                        .ok_or_else(|| format!("unknown label '{label}' in pattern '{s}'"))
                };
                items.push(Item::Range(endpoint(start)?, endpoint(end)?));
            } else {
                items.push(Item::Glob(item.as_bytes().to_vec()));
            }
        }
        Ok(Pattern { items })
    }

    /// Returns whether a statement with the given label and database position
    /// matches the pattern.
    pub fn matches(&self, label: &[u8], pos: u32) -> bool {
        self.items.iter().any(|item| match item {
            Item::Glob(glob) => glob_match(glob, label),
            Item::Range(start, end) => {
                start.is_none_or(|start| start <= pos) && end.is_none_or(|end| pos <= end)
            }
        })
    }
}

/// Matches `s` against a glob in which `*` matches any sequence of characters
/// and `?` matches any single character.
fn glob_match(glob: &[u8], s: &[u8]) -> bool {
    let (mut g, mut i) = (0, 0);
    // The position just after the last `*` seen, and the position in `s` that
    // it is currently matched up to, for backtracking.
    let mut star: Option<(usize, usize)> = None;
    while i < s.len() {
        match glob.get(g) {
            Some(b'*') => {
                g += 1;
                star = Some((g, i));
            }
            Some(&c) if c == b'?' || c == s[i] => {
                g += 1;
                i += 1;
            }
            _ => match star {
                // Let the last `*` absorb one more character and retry.
                Some((sg, si)) => {
                    g = sg;
                    i = si + 1;
                    star = Some((sg, si + 1));
                }
                None => return false,
            },
        }
    }
    glob[g..].iter().all(|&c| c == b'*')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs() {
        assert!(glob_match(b"df-*", b"df-an"));
        assert!(!glob_match(b"df-*", b"dfan"));
        assert!(glob_match(b"df-an", b"df-an"));
        assert!(!glob_match(b"df-an", b"df-and"));
        assert!(glob_match(b"*", b""));
        assert!(glob_match(b"a*b*c", b"abc"));
        assert!(glob_match(b"a*b*c", b"axxbyyc"));
        assert!(!glob_match(b"a*b*c", b"axxcyyb"));
        assert!(!glob_match(b"ab*ba", b"aba"));
        assert!(glob_match(b"df-?n", b"df-an"));
        assert!(!glob_match(b"df-?n", b"df-n"));
        assert!(!glob_match(b"df-?", b"df-an"));
        assert!(glob_match(b"?*", b"a"));
        assert!(!glob_match(b"?*", b""));
        assert!(glob_match(b"*?b", b"abab"));
        assert!(!glob_match(b"*?b", b"b"));
        assert!(glob_match(b"a*?c", b"abcc"));
    }

    #[test]
    fn ranges_and_lists() {
        let resolve = |l: &[u8]| match l {
            b"a" => Some(10),
            b"b" => Some(20),
            _ => None,
        };
        let p = Pattern::parse("a~b,df-*", resolve).unwrap();
        assert!(p.matches(b"x", 10));
        assert!(p.matches(b"x", 20));
        assert!(!p.matches(b"x", 21));
        assert!(p.matches(b"df-x", 99));
        let p = Pattern::parse("~a", resolve).unwrap();
        assert!(p.matches(b"x", 0));
        assert!(!p.matches(b"x", 11));
        let p = Pattern::parse("b~", resolve).unwrap();
        assert!(p.matches(b"x", 1000));
        assert!(Pattern::parse("c~", resolve).is_err());
        assert!(Pattern::parse("a,,b", resolve).is_err());
    }
}
