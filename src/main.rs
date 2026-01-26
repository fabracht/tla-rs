use std::collections::BTreeSet;
use std::env;
use std::fs;
#[cfg(not(target_arch = "wasm32"))]
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use tlc_executor::ast::{Env, Value};
use tlc_executor::checker::{check, format_eval_error, format_trace, format_trace_with_diffs, CheckResult, CheckerConfig};
use tlc_executor::diagnostic::Diagnostic;
use tlc_executor::parser::parse;
use tlc_executor::Source;

fn split_top_level(s: &str, delim: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut in_string = false;

    for c in s.chars() {
        if c == '"' && depth == 0 {
            in_string = !in_string;
            current.push(c);
        } else if in_string {
            current.push(c);
        } else if c == '{' {
            depth += 1;
            current.push(c);
        } else if c == '}' {
            depth -= 1;
            current.push(c);
        } else if c == delim && depth == 0 {
            parts.push(current.trim().to_string());
            current = String::new();
        } else {
            current.push(c);
        }
    }
    if !current.trim().is_empty() {
        parts.push(current.trim().to_string());
    }
    parts
}

fn parse_constant_value(s: &str) -> Option<Value> {
    let s = s.trim();
    if let Ok(n) = s.parse::<i64>() {
        return Some(Value::Int(n));
    }
    if s == "TRUE" {
        return Some(Value::Bool(true));
    }
    if s == "FALSE" {
        return Some(Value::Bool(false));
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner: Arc<str> = s[1..s.len() - 1].into();
        return Some(Value::Str(inner));
    }
    if s.starts_with('{') && s.ends_with('}') {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Some(Value::Set(BTreeSet::new()));
        }
        let mut set = BTreeSet::new();
        for part in split_top_level(inner, ',') {
            if let Some(val) = parse_constant_value(&part) {
                set.insert(val);
            } else {
                return None;
            }
        }
        return Some(Value::Set(set));
    }
    None
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <spec.tla> [--constant NAME=VALUE] [--symmetry CONST] [--max-states N] [--export-dot FILE] [--allow-deadlock] [--check-liveness]", args[0]);
        return ExitCode::FAILURE;
    }

    let mut config = CheckerConfig::new();
    let mut spec_path = None;
    let mut constants: Vec<(Arc<str>, Value)> = Vec::new();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--constant" | "-c" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--constant requires NAME=VALUE");
                    return ExitCode::FAILURE;
                }
                let arg = &args[i];
                if let Some(eq_pos) = arg.find('=') {
                    let name: Arc<str> = arg[..eq_pos].into();
                    let val_str = &arg[eq_pos + 1..];
                    match parse_constant_value(val_str) {
                        Some(val) => constants.push((name, val)),
                        None => {
                            eprintln!("invalid constant value: {}", val_str);
                            eprintln!("supported formats: integer, TRUE, FALSE, \"string\", {{1,2,3}}");
                            return ExitCode::FAILURE;
                        }
                    }
                } else {
                    eprintln!("--constant requires NAME=VALUE format");
                    return ExitCode::FAILURE;
                }
            }
            "--max-states" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--max-states requires a value");
                    return ExitCode::FAILURE;
                }
                config.max_states = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid value for --max-states");
                    std::process::exit(1);
                });
            }
            "--max-depth" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--max-depth requires a value");
                    return ExitCode::FAILURE;
                }
                config.max_depth = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid value for --max-depth");
                    std::process::exit(1);
                });
            }
            "--symmetry" | "-s" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--symmetry requires a constant name");
                    return ExitCode::FAILURE;
                }
                let name: Arc<str> = args[i].clone().into();
                config.symmetric_constants.push(name);
            }
            #[cfg(not(target_arch = "wasm32"))]
            "--export-dot" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--export-dot requires a filename");
                    return ExitCode::FAILURE;
                }
                config.export_dot_path = Some(PathBuf::from(&args[i]));
            }
            "--allow-deadlock" => {
                config.allow_deadlock = true;
            }
            "--check-liveness" => {
                config.check_liveness = true;
            }
            "--help" | "-h" => {
                println!("tlc-executor - TLA+ model checker");
                println!();
                println!("Usage: {} <spec.tla> [options]", args[0]);
                println!();
                println!("Options:");
                println!("  --constant, -c NAME=VALUE  Set a constant value");
                println!("                             Formats: 3, TRUE, FALSE, \"str\", {{1,2,3}}");
                println!("  --symmetry, -s CONST       Enable symmetry reduction for a constant");
                println!("                             Can be used multiple times for multiple constants");
                println!("  --max-states N             Maximum states to explore (default: 1000000)");
                println!("  --max-depth N              Maximum trace depth (default: 100)");
                println!("  --export-dot FILE          Export state graph to DOT format");
                println!("  --allow-deadlock           Allow states with no successors");
                println!("  --check-liveness           Check liveness and fairness properties");
                println!("  --help, -h                 Show this help");
                return ExitCode::SUCCESS;
            }
            arg if arg.starts_with('-') => {
                eprintln!("unknown option: {}", arg);
                return ExitCode::FAILURE;
            }
            path => {
                spec_path = Some(path.to_string());
            }
        }
        i += 1;
    }

    let spec_path = match spec_path {
        Some(p) => p,
        None => {
            eprintln!("no spec file provided");
            return ExitCode::FAILURE;
        }
    };

    let input = match fs::read_to_string(&spec_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("failed to read {}: {}", spec_path, e);
            return ExitCode::FAILURE;
        }
    };

    let source = Source::new(spec_path.as_str(), input.as_str());

    let spec = match parse(&input) {
        Ok(s) => s,
        Err(e) => {
            let mut diag = Diagnostic::error(&e.message);
            if let Some(span) = e.span {
                diag = diag.with_span(span);
            }
            if let Some(expected) = &e.expected
                && let Some(found) = &e.found
            {
                diag = diag.with_label(format!("expected {}, found {}", expected, found));
            }
            eprintln!("{}", diag.render(&source));
            return ExitCode::FAILURE;
        }
    };

    println!("Checking spec: {}", spec_path);
    if !spec.extends.is_empty() {
        println!("  Extends: {}", spec.extends.iter().map(|s| s.as_ref()).collect::<Vec<_>>().join(", "));
    }
    println!("  Variables: {}", spec.vars.iter().map(|s| s.as_ref()).collect::<Vec<_>>().join(", "));
    if !spec.constants.is_empty() {
        println!("  Constants: {}", spec.constants.iter().map(|s| s.as_ref()).collect::<Vec<_>>().join(", "));
    }
    println!("  Invariants: {}", spec.invariants.len());
    println!();

    let mut domains = Env::new();
    for (name, val) in constants {
        domains.insert(name, val);
    }
    let result = check(&spec, &domains, &config);

    match result {
        CheckResult::Ok(stats) => {
            println!("Model checking complete. No errors found.");
            println!();
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Max depth: {}", stats.max_depth_reached);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            ExitCode::SUCCESS
        }
        CheckResult::InvariantViolation(cex, stats) => {
            let inv_name = spec
                .invariant_names
                .get(cex.violated_invariant)
                .and_then(|n| n.as_ref())
                .map(|n| n.as_ref())
                .unwrap_or("(unnamed)");
            println!("Invariant {} ({}) violated!", cex.violated_invariant, inv_name);
            println!();
            println!("Counterexample trace ({} states):", cex.trace.len());
            println!("  (* marks changed variables)");
            println!();
            print!("{}", format_trace_with_diffs(&cex.trace, &spec.vars));
            println!();
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            ExitCode::FAILURE
        }
        CheckResult::LivenessViolation(violation, stats) => {
            println!("Liveness property violated: {}", violation.property);
            println!();
            println!("Prefix trace ({} states):", violation.prefix.len());
            println!("  (* marks changed variables)");
            println!();
            print!("{}", format_trace_with_diffs(&violation.prefix, &spec.vars));
            println!();
            println!("Cycle ({} states):", violation.cycle.len());
            println!();
            print!("{}", format_trace_with_diffs(&violation.cycle, &spec.vars));
            println!();
            if !violation.fairness_info.is_empty() {
                println!("Fairness information:");
                for (info, taken) in &violation.fairness_info {
                    let status = if *taken { "satisfied" } else { "violated" };
                    println!("  {}: {}", info, status);
                }
                println!();
            }
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            ExitCode::FAILURE
        }
        CheckResult::Deadlock(trace, stats) => {
            println!("Deadlock detected!");
            println!();
            println!("Trace to deadlock state ({} states):", trace.len());
            println!("  (* marks changed variables)");
            println!();
            print!("{}", format_trace_with_diffs(&trace, &spec.vars));
            println!();
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            println!();
            println!("Use --allow-deadlock to suppress this error.");
            ExitCode::FAILURE
        }
        CheckResult::InitError(e) => {
            eprintln!("error: evaluating Init");
            eprintln!("  {}", format_eval_error(&e));
            ExitCode::FAILURE
        }
        CheckResult::NextError(e, trace) => {
            eprintln!("error: evaluating Next");
            eprintln!("  {}", format_eval_error(&e));
            eprintln!();
            eprintln!("State when error occurred:");
            print!("{}", format_trace(&trace, &spec.vars));
            ExitCode::FAILURE
        }
        CheckResult::InvariantError(e, trace) => {
            eprintln!("error: evaluating invariant");
            eprintln!("  {}", format_eval_error(&e));
            eprintln!();
            eprintln!("State when error occurred:");
            print!("{}", format_trace(&trace, &spec.vars));
            ExitCode::FAILURE
        }
        CheckResult::MaxStatesExceeded(stats) => {
            println!("State limit exceeded ({} states)", config.max_states);
            println!();
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Max depth: {}", stats.max_depth_reached);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            println!();
            println!("Increase with --max-states N");
            ExitCode::FAILURE
        }
        CheckResult::MaxDepthExceeded(stats) => {
            println!("Depth limit exceeded ({} levels)", config.max_depth);
            println!();
            println!("  States explored: {}", stats.states_explored);
            println!("  Transitions: {}", stats.transitions);
            println!("  Time: {:.3}s", stats.elapsed_secs);
            println!();
            println!("Increase with --max-depth N");
            ExitCode::FAILURE
        }
        CheckResult::NoInitialStates => {
            eprintln!("No initial states found. Check your Init predicate.");
            ExitCode::FAILURE
        }
        CheckResult::MissingConstants(missing) => {
            eprintln!("Missing constant values:");
            for c in &missing {
                eprintln!("  {}", c);
            }
            eprintln!();
            eprintln!("Provide values with --constant NAME=VALUE");
            ExitCode::FAILURE
        }
        CheckResult::AssumeViolation(idx) => {
            eprintln!("ASSUME {} evaluated to FALSE", idx);
            eprintln!();
            eprintln!("Check your constant values or ASSUME constraints.");
            ExitCode::FAILURE
        }
        CheckResult::AssumeError(idx, e) => {
            eprintln!("error: evaluating ASSUME {}", idx);
            eprintln!("  {}", format_eval_error(&e));
            ExitCode::FAILURE
        }
    }
}
