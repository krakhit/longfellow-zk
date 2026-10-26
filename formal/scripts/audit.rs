//! Scan repository Lean sources for unchecked proof constructs and check local
//! Markdown links in the formal and Rust documentation. Run inside the repo.
use std::{collections::BTreeSet, fs, path::Path, process::Command};

fn code(source: &str) -> String {
    let mut bytes = source.as_bytes().to_vec();
    let (mut i, mut depth, mut line, mut string) = (0, 0, false, false);
    while i < bytes.len() {
        if bytes[i] == b'\n' {
            line = false;
            i += 1;
            continue;
        }
        if line {
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                bytes[i] = b' ';
                bytes[i + 1] = b' ';
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                string = false;
            }
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i..i + 2] == *b"/-" {
            depth += 1;
            bytes[i] = b' ';
            bytes[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth > 0 {
            if i + 1 < bytes.len() && bytes[i..i + 2] == *b"-/" {
                depth -= 1;
                bytes[i] = b' ';
                bytes[i + 1] = b' ';
                i += 2;
                continue;
            }
            bytes[i] = b' ';
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i..i + 2] == *b"--" {
            line = true;
            continue;
        }
        if bytes[i] == b'"' {
            string = true;
            bytes[i] = b' ';
        }
        i += 1;
    }
    String::from_utf8(bytes).unwrap()
}

fn main() {
    let root = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .unwrap();
    assert!(root.status.success());
    std::env::set_current_dir(std::str::from_utf8(&root.stdout).unwrap().trim()).unwrap();
    let output = Command::new("git")
        .args([
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let paths: BTreeSet<_> = std::str::from_utf8(&output.stdout)
        .unwrap()
        .split('\0')
        .filter(|p| !p.is_empty() && Path::new(p).is_file())
        .collect();
    let (mut lean_count, mut link_count, mut failures) = (0, 0, 0);
    for name in paths {
        let path = Path::new(name);
        if name.starts_with("formal/") && name.ends_with(".lean") {
            lean_count += 1;
            let source = code(&fs::read_to_string(path).unwrap());
            for (line, text) in source.lines().enumerate() {
                for word in text.split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'') {
                    if ["sorry", "sorryAx", "admit", "axiom", "unsafe"].contains(&word) {
                        eprintln!("{name}:{}: unchecked construct {word}", line + 1);
                        failures += 1;
                    }
                }
            }
        }
        if name.ends_with(".md")
            && (name.starts_with("formal/") || name.starts_with("rust/") || name == "README.md")
        {
            let source = fs::read_to_string(path).unwrap();
            for (line, text) in source.lines().enumerate() {
                for suffix in text.split("](").skip(1) {
                    let Some((target, _)) = suffix.split_once(')') else {
                        continue;
                    };
                    let target = target.trim().trim_matches(['<', '>']);
                    if target.starts_with('#')
                        || target.contains("://")
                        || target.starts_with("mailto:")
                    {
                        continue;
                    }
                    let file = target.split('#').next().unwrap();
                    if file.is_empty() {
                        continue;
                    }
                    link_count += 1;
                    if !path.parent().unwrap().join(file).exists() {
                        eprintln!("{name}:{}: missing link target {target}", line + 1);
                        failures += 1;
                    }
                }
            }
        }
    }
    println!("Scanned {lean_count} Lean sources and {link_count} local documentation links.");
    assert!(lean_count > 0, "no Lean sources found");
    assert_eq!(failures, 0, "source/documentation audit failed");
}
