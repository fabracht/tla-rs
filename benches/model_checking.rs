use std::collections::BTreeSet;
use std::sync::Arc;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use tlc_executor::ast::{Env, Value};
use tlc_executor::checker::{check, CheckerConfig, CheckResult};
use tlc_executor::parser::parse;

fn quiet_config() -> CheckerConfig {
    CheckerConfig {
        quiet: true,
        ..CheckerConfig::default()
    }
}

fn bench_large_counter(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/benchmark/large_counter.tla");
    let spec = parse(spec_text).expect("failed to parse large_counter.tla");

    let mut group = c.benchmark_group("large_counter");
    for max in [5, 10, 15, 20] {
        let mut env = Env::new();
        env.insert(Arc::from("MAX"), Value::Int(max));

        group.bench_with_input(BenchmarkId::new("max", max), &env, |b, env| {
            b.iter(|| {
                let config = CheckerConfig {
                    allow_deadlock: true,
                    ..quiet_config()
                };
                check(&spec, env, &config)
            });
        });
    }
    group.finish();
}

fn bench_symmetric_procs(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/benchmark/symmetric_procs.tla");
    let spec = parse(spec_text).expect("failed to parse symmetric_procs.tla");

    let proc_set: BTreeSet<Value> = ["a", "b", "c"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut env = Env::new();
    env.insert(Arc::from("Proc"), Value::Set(proc_set));

    let mut group = c.benchmark_group("symmetric_procs");

    group.bench_function("3_procs_no_symmetry", |b| {
        b.iter(|| {
            let config = CheckerConfig {
                allow_deadlock: true,
                ..quiet_config()
            };
            check(&spec, &env, &config)
        });
    });

    group.bench_function("3_procs_with_symmetry", |b| {
        b.iter(|| {
            let config = CheckerConfig {
                symmetric_constants: vec![Arc::from("Proc")],
                allow_deadlock: true,
                ..quiet_config()
            };
            check(&spec, &env, &config)
        });
    });

    group.finish();
}

fn bench_diehard(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/official/DieHard.tla");
    let spec = parse(spec_text).expect("failed to parse DieHard.tla");

    let env = Env::new();
    let mut group = c.benchmark_group("official");

    group.bench_function("diehard", |b| {
        b.iter(|| {
            let config = quiet_config();
            check(&spec, &env, &config)
        });
    });

    group.finish();
}

fn bench_tcommit(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/official/TCommit.tla");
    let spec = parse(spec_text).expect("failed to parse TCommit.tla");

    let mut group = c.benchmark_group("tcommit");

    for rm_count in [2, 3, 4] {
        let rm_set: BTreeSet<Value> = (1..=rm_count)
            .map(|i| Value::Str(Arc::from(format!("rm{}", i))))
            .collect();

        let mut env = Env::new();
        env.insert(Arc::from("RM"), Value::Set(rm_set));

        group.bench_with_input(BenchmarkId::new("rm_count", rm_count), &env, |b, env| {
            b.iter(|| {
                let config = CheckerConfig {
                    allow_deadlock: true,
                    ..quiet_config()
                };
                check(&spec, env, &config)
            });
        });
    }

    group.finish();
}

#[allow(dead_code)]
fn validate_benchmarks() {
    let large_counter_text = include_str!("../test_cases/benchmark/large_counter.tla");
    let large_counter = parse(large_counter_text).expect("failed to parse large_counter.tla");
    let mut env = Env::new();
    env.insert(Arc::from("MAX"), Value::Int(5));
    let config = CheckerConfig {
        allow_deadlock: true,
        quiet: true,
        ..CheckerConfig::default()
    };
    let result = check(&large_counter, &env, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 216);
        }
        other => panic!("large_counter should pass, got {:?}", other),
    }

    let diehard_text = include_str!("../test_cases/official/DieHard.tla");
    let diehard = parse(diehard_text).expect("failed to parse DieHard.tla");
    let env = Env::new();
    let config = CheckerConfig {
        quiet: true,
        ..CheckerConfig::default()
    };
    let result = check(&diehard, &env, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 16);
        }
        other => panic!("diehard should pass, got {:?}", other),
    }
}

criterion_group!(
    benches,
    bench_large_counter,
    bench_symmetric_procs,
    bench_diehard,
    bench_tcommit
);

criterion_main!(benches);

#[test]
fn test_benchmarks_validity() {
    validate_benchmarks();
}
