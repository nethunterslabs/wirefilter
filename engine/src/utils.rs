pub(crate) fn escape(string: &str, hex_and_oct: bool) -> String {
    let mut res = String::new();
    for c in string.chars() {
        match c {
            '\n' => res.push(c),
            '\x00'..='\x1f' | '\x7f' if hex_and_oct => {
                res.push('\\');
                res.push('x');
                res.push_str(&format!("{:02x}", c as u8));
            }
            '\x20'..='\x7e' => match c {
                '\\' if hex_and_oct => {
                    res.push_str(r"\\");
                }
                '"' => {
                    res.push_str(r#"\""#);
                }
                _ => {
                    res.push(c);
                }
            },
            _ => {
                res.push(c);
            }
        }
    }
    res
}
