use std::process::Command;

fn run_args(bin: &str, args: &[&str]) -> (bool, String, String) {
    let output = Command::new(bin)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run {bin} {args:?}: {e}"));
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).trim().to_string(),
        String::from_utf8_lossy(&output.stderr).trim().to_string(),
    )
}

fn run(bin: &str, flag: &str) -> (bool, String, String) {
    run_args(bin, &[flag])
}

#[test]
fn tla_version_flags_print_package_version_and_exit_zero() {
    let expected = format!("tla {}", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let (ok, stdout, stderr) = run(env!("CARGO_BIN_EXE_tla"), flag);
        assert!(ok, "tla {flag} must exit 0; stderr:\n{stderr}");
        assert_eq!(
            stdout, expected,
            "tla {flag} must print the package version; stderr:\n{stderr}"
        );
    }
}

#[test]
fn tla_mcp_version_flags_print_package_version_and_exit_zero() {
    let expected = format!("tla-mcp {}", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let (ok, stdout, stderr) = run(env!("CARGO_BIN_EXE_tla-mcp"), flag);
        assert!(ok, "tla-mcp {flag} must exit 0; stderr:\n{stderr}");
        assert_eq!(
            stdout, expected,
            "tla-mcp {flag} must print the package version instead of starting the stdio server; stderr:\n{stderr}"
        );
    }
}

#[test]
fn tla_mcp_rejects_an_unknown_option_instead_of_serving() {
    let (ok, _stdout, stderr) = run(env!("CARGO_BIN_EXE_tla-mcp"), "--verison");
    assert!(!ok, "tla-mcp must reject an unknown option");
    assert!(
        stderr.contains("unknown option: --verison"),
        "tla-mcp must name the rejected option rather than starting the stdio server; stderr:\n{stderr}"
    );
}

#[test]
fn tla_does_not_swallow_a_flag_as_a_value_taking_flags_argument() {
    for flag in [
        "--symmetry",
        "--max-states",
        "--count-satisfying",
        "--config",
    ] {
        let (ok, stdout, stderr) = run_args(env!("CARGO_BIN_EXE_tla"), &[flag, "--version"]);
        assert!(
            !ok,
            "tla {flag} --version must not exit 0; stderr:\n{stderr}"
        );
        assert!(
            stderr.contains(&format!("{flag} requires")),
            "tla {flag} --version must report the missing value for {flag}; stderr:\n{stderr}"
        );
        assert!(
            !stdout.contains(env!("CARGO_PKG_VERSION")),
            "tla {flag} --version must not consume --version as a value; stdout:\n{stdout}"
        );
    }
}

#[test]
fn tla_help_lists_the_version_flag() {
    let (ok, stdout, stderr) = run(env!("CARGO_BIN_EXE_tla"), "--help");
    assert!(ok, "tla --help must exit 0; stderr:\n{stderr}");
    assert!(
        stdout.contains("--version, -V"),
        "--help must advertise the version flag; got:\n{stdout}"
    );
}
