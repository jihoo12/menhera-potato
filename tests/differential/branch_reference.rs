//! Reference checks paired with the unchanged Rust branch-audit assertions.
use std::path::Path;
use std::process::Command;

pub fn assert_agda(case: &str, accepts: bool, rejection: &str) {
    let installed = "/home/user/.cabal/bin/agda";
    let agda = if Path::new(installed).exists() {
        installed
    } else {
        "agda"
    };
    let output = Command::new(agda)
        .args(["--no-libraries", "-i", "tests/differential/cases"])
        .arg(format!("tests/differential/cases/{case}.agda"))
        .output()
        .expect("Agda must run for the branch telescope differential check");
    let diagnostics = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.status.success(),
        accepts,
        "Agda {case}: {diagnostics}"
    );
    if !accepts {
        // A parser/import failure must not count as rejection of the bad term.
        assert!(
            diagnostics.contains(rejection),
            "unexpected Agda rejection for {case}: {diagnostics}"
        );
    }
}
