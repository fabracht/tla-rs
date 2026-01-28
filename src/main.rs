#[cfg(feature = "dhat")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use std::collections::BTreeSet;
use std::env;
use std::fs;
#[cfg(not(target_arch = "wasm32"))]
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use tlc_executor::ast::{Env, Value};
use tlc_executor::checker::{check, check_result_to_json, eval_error_to_diagnostic, format_eval_error, format_trace, format_trace_with_diffs, write_trace_json, CheckResult, CheckerConfig};
use tlc_executor::diagnostic::Diagnostic;
use tlc_executor::parser::parse;
use tlc_executor::scenario::{execute_scenario, format_scenario_result, parse_scenario};
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

fn is_likely_subcommand(arg: &str) -> bool {
    ["check", "run", "verify", "parse", "lint", "test"]
        .contains(&arg.to_lowercase().as_str())
}

fn main() -> ExitCode {
    #[cfg(feature = "dhat")]
    let _profiler = dhat::Profiler::new_heap();

    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <spec.tla> [--constant NAME=VALUE] [--symmetry CONST] [--max-states N] [--export-dot FILE] [--allow-deadlock] [--check-liveness]", args[0]);
        return ExitCode::FAILURE;
    }

    let mut config = CheckerConfig::new();
    let mut spec_path = None;
    let mut constants: Vec<(Arc<str>, Value)> = Vec::new();
    let mut scenario_input: Option<String> = None;
    let mut validate_only = false;
    let mut list_invariants = false;

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
            "--quick" | "-q" => {
                config.max_states = 10_000;
                config.quick_mode = true;
            }
            "--verbose" | "-v" => {
                config.verbosity = 2;
            }
            "-vv" => {
                config.verbosity = 3;
            }
            "--json" => {
                config.json_output = true;
            }
            "--validate" => {
                validate_only = true;
            }
            "--list-invariants" => {
                list_invariants = true;
            }
            #[cfg(not(target_arch = "wasm32"))]
            "--trace-json" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--trace-json requires a filename");
                    return ExitCode::FAILURE;
                }
                config.trace_json_path = Some(PathBuf::from(&args[i]));
            }
            "--scenario" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--scenario requires a scenario string or @filename");
                    return ExitCode::FAILURE;
                }
                let arg = &args[i];
                if let Some(filename) = arg.strip_prefix('@') {
                    match fs::read_to_string(filename) {
                        Ok(content) => scenario_input = Some(content),
                        Err(e) => {
                            eprintln!("failed to read scenario file {}: {}", filename, e);
                            return ExitCode::FAILURE;
                        }
                    }
                } else {
                    scenario_input = Some(arg.clone());
                }
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
                println!("  --trace-json FILE          Export counterexample trace to JSON format");
                println!("  --allow-deadlock           Allow states with no successors");
                println!("  --check-liveness           Check liveness and fairness properties");
                println!("  --quick, -q                Quick exploration (limit: 10,000 states)");
                println!("  --verbose, -v              Verbose output (show more details)");
                println!("  -vv                        Debug output (show all details)");
                println!("  --json                     Output results in JSON format");
                println!("  --validate                 Parse and validate spec without model checking");
                println!("  --list-invariants          Show detected invariants and exit");
                println!("  --scenario TEXT            Explore a specific scenario (or @file)");
                println!("  --help, -h                 Show this help");
                println!();
                println!("Scenario format:");
                println!("  step: <TLA+ expression>    Match transition where expression is TRUE");
                println!();
                println!("  Variables: unprimed = current state, primed = next state");
                println!();
                println!("  Examples:");
                println!("    step: x' > x                    # x increases");
                println!("    step: \"s1\" \\in active'          # s1 becomes active");
                println!("    step: pc'[\"p1\"] = \"critical\"    # p1 enters critical section");
                println!("    step: count' = count + 1        # count increments by 1");
                println!("    step: x' # x                    # x changes (any value)");
                return ExitCode::SUCCESS;
            }
            arg if arg.starts_with('-') => {
                eprintln!("unknown option: {}", arg);
                eprintln!("Use --help for available options");
                return ExitCode::FAILURE;
            }
            path => {
                if spec_path.is_none() && is_likely_subcommand(path) {
                    eprintln!(
                        "error: '{}' looks like a subcommand, but tlc-executor doesn't use subcommands.",
                        path
                    );
                    eprintln!();
                    eprintln!("Usage: {} <spec.tla> [options]", args[0]);
                    eprintln!();
                    eprintln!("Example: {} yourspec.tla --max-states 10000", args[0]);
                    eprintln!("         {} yourspec.tla --quick", args[0]);
                    return ExitCode::FAILURE;
                }
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

    let mut domains = Env::new();
    for (name, val) in constants {
        domains.insert(name, val);
    }

    if list_invariants {
        println!("Invariants detected in {}:", spec_path);
        if spec.invariants.is_empty() {
            println!("  (none)");
        } else {
            for (i, name) in spec.invariant_names.iter().enumerate() {
                let name_str = name.as_ref().map(|n| n.as_ref()).unwrap_or("(unnamed)");
                println!("  {}: {}", i, name_str);
            }
        }
        return ExitCode::SUCCESS;
    }

    if validate_only {
        println!("Validating spec: {}", spec_path);
        println!();

        let mut has_issues = false;

        if spec.vars.is_empty() {
            eprintln!("  Warning: no VARIABLES declared");
            has_issues = true;
        } else {
            println!("  Variables: {} declared", spec.vars.len());
        }

        let missing: Vec<_> = spec
            .constants
            .iter()
            .filter(|c| !domains.contains_key(c.as_ref()))
            .collect();
        if !missing.is_empty() {
            eprintln!("  Missing constants: {}", missing.iter().map(|c| c.as_ref()).collect::<Vec<_>>().join(", "));
            has_issues = true;
        } else if !spec.constants.is_empty() {
            println!("  Constants: {} provided", spec.constants.len());
        }

        println!("  Invariants: {} detected", spec.invariants.len());
        println!("  Definitions: {} declared", spec.definitions.len());

        if !spec.assumes.is_empty() {
            println!("  ASSUME expressions: {}", spec.assumes.len());
        }

        if has_issues {
            println!();
            println!("Validation found issues (see warnings above)");
            return ExitCode::FAILURE;
        }

        println!();
        println!("Validation passed");
        return ExitCode::SUCCESS;
    }

    if let Some(scenario_text) = scenario_input {
        println!("Scenario exploration: {}", spec_path);
        println!();

        let scenario = match parse_scenario(&scenario_text) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error parsing scenario: {}", e);
                return ExitCode::FAILURE;
            }
        };

        println!("Scenario steps: {}", scenario.steps.len());
        for (i, step) in scenario.steps.iter().enumerate() {
            println!("  {}. {:?}", i + 1, step);
        }
        println!();

        match execute_scenario(&spec, &scenario, &domains) {
            Ok(result) => {
                let vars_of_interest: Vec<&str> = spec.vars.iter().map(|s| s.as_ref()).collect();
                println!("{}", format_scenario_result(&result, &vars_of_interest, &spec.vars));
                if result.failure.is_some() {
                    return ExitCode::FAILURE;
                }
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                eprintln!("error executing scenario: {}", format_eval_error(&e));
                return ExitCode::FAILURE;
            }
        }
    }

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

    config.spec_path = Some(PathBuf::from(&spec_path));
    let result = check(&spec, &domains, &config);

    #[cfg(feature = "profiling")]
    {
        println!();
        tlc_executor::report_profiling_stats();
    }

    if config.json_output {
        println!("{}", check_result_to_json(&result, &spec));
        return match &result {
            CheckResult::Ok(_) | CheckResult::MaxStatesExceeded(_) if config.quick_mode => ExitCode::SUCCESS,
            CheckResult::Ok(_) => ExitCode::SUCCESS,
            _ => ExitCode::FAILURE,
        };
    }

    if let Some(ref trace_path) = config.trace_json_path {
        let trace = match &result {
            CheckResult::InvariantViolation(cex, _) => Some(&cex.trace),
            CheckResult::Deadlock(trace, _) => Some(trace),
            CheckResult::NextError(_, trace) => Some(trace),
            CheckResult::InvariantError(_, trace) => Some(trace),
            _ => None,
        };
        if let Some(trace) = trace {
            if let Err(e) = write_trace_json(trace_path, trace, &spec.vars) {
                eprintln!("failed to write trace JSON to {}: {}", trace_path.display(), e);
            } else if config.verbosity >= 2 {
                println!("Trace written to {}", trace_path.display());
            }
        }
    }

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
            let diag = eval_error_to_diagnostic(&e);
            eprintln!("error evaluating Init: {}", diag.render_simple());
            ExitCode::FAILURE
        }
        CheckResult::NextError(e, trace) => {
            let diag = eval_error_to_diagnostic(&e);
            eprintln!("error evaluating Next: {}", diag.render_simple());
            eprintln!();
            eprintln!("State when error occurred:");
            print!("{}", format_trace(&trace, &spec.vars));
            ExitCode::FAILURE
        }
        CheckResult::InvariantError(e, trace) => {
            let diag = eval_error_to_diagnostic(&e);
            eprintln!("error evaluating invariant: {}", diag.render_simple());
            eprintln!();
            eprintln!("State when error occurred:");
            print!("{}", format_trace(&trace, &spec.vars));
            ExitCode::FAILURE
        }
        CheckResult::MaxStatesExceeded(stats) => {
            if config.quick_mode {
                println!("Quick mode: explored {} states", stats.states_explored);
                println!();
                println!("Summary of explored state space:");
                println!("  States explored: {}", stats.states_explored);
                println!("  Transitions: {}", stats.transitions);
                println!("  Max depth: {}", stats.max_depth_reached);
                println!("  Time: {:.3}s", stats.elapsed_secs);
                println!();
                println!("  No invariant violations found in explored states.");
                println!();
                println!("To continue exploration:");
                println!("  --max-states {}   Explore more states", config.max_states * 2);
                ExitCode::SUCCESS
            } else {
                println!("State limit reached ({} states)", config.max_states);
                println!();
                println!("Summary of explored state space:");
                println!("  States explored: {}", stats.states_explored);
                println!("  Transitions: {}", stats.transitions);
                println!("  Max depth: {}", stats.max_depth_reached);
                println!("  Time: {:.3}s", stats.elapsed_secs);
                println!();
                println!("  No invariant violations found in explored states.");
                println!();
                println!("To continue exploration:");
                println!("  --max-states {}   Double the limit", config.max_states * 2);
                println!();
                println!("To reduce state space:");
                println!("  --symmetry CONST     Enable symmetry reduction");
                ExitCode::FAILURE
            }
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
            eprintln!("No initial states found.");
            eprintln!();
            eprintln!("Possible causes:");
            eprintln!("  - Init predicate evaluates to FALSE for all variable combinations");
            if !spec.constants.is_empty() {
                let missing: Vec<_> = spec.constants.iter().filter(|c| !domains.contains_key(c.as_ref())).collect();
                if !missing.is_empty() {
                    eprintln!("  - Missing constant values: {}", missing.iter().map(|c| c.as_ref()).collect::<Vec<_>>().join(", "));
                }
            }
            eprintln!("  - Type error or domain error in Init expression");
            eprintln!();
            eprintln!("Suggestions:");
            eprintln!("  - Verify Init predicate can be satisfied");
            eprintln!("  - Check that all constants have appropriate values");
            eprintln!("  - Use --validate to check spec structure");
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
            eprintln!("ASSUME violation: constraint {} evaluated to FALSE", idx);
            eprintln!();
            if let Some(assume_expr) = spec.assumes.get(idx) {
                eprintln!("Expression: {:?}", assume_expr);
                eprintln!();
            }
            eprintln!("The ASSUME constraint is not satisfied by the current constant values.");
            eprintln!();
            eprintln!("Suggestions:");
            eprintln!("  - Check that --constant values satisfy all ASSUME constraints");
            eprintln!("  - Verify the ASSUME expression is correct");
            ExitCode::FAILURE
        }
        CheckResult::AssumeError(idx, e) => {
            let diag = eval_error_to_diagnostic(&e);
            eprintln!("error evaluating ASSUME {}: {}", idx, diag.render_simple());
            eprintln!();
            if let Some(assume_expr) = spec.assumes.get(idx) {
                eprintln!("Expression: {:?}", assume_expr);
                eprintln!();
            }
            eprintln!("An error occurred while evaluating the ASSUME constraint.");
            ExitCode::FAILURE
        }
    }
}
