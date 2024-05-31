pub(crate) fn escape_hex_and_oct(string: &str) -> String {
    let mut res = String::new();
    for c in string.chars() {
        match c {
            '\n' => res.push(c),
            '\x00'..='\x1f' | '\x7f' => {
                res.push('\\');
                res.push('x');
                res.push_str(&format!("{:02x}", c as u8));
            }
            '\x20'..='\x7e' => res.push(c),
            _ => {
                if c == '"' {
                    res.push('\\');
                    res.push(c);
                } else {
                    res.push(c);
                }
            }
        }
    }
    res
}
