use std::collections::BTreeSet;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::Path;
use std::sync::Arc;

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use tla_checker::ast::{Env, Expr, State, Value};
use tla_checker::checker::{CheckResult, CheckerConfig, check};
use tla_checker::eval::{Definitions, eval};
use tla_checker::parser::parse;
use tla_checker::symmetry::SymmetryConfig;

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

    let param_path = Path::new("test_cases/should_pass/parameterized_instance.tla");
    let param_text =
        std::fs::read_to_string(param_path).expect("failed to read parameterized_instance.tla");
    let param_spec = parse(&param_text).expect("failed to parse parameterized_instance.tla");
    let id_set: BTreeSet<Value> = ["a", "b"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();
    let mut env = Env::new();
    env.insert(Arc::from("Ids"), Value::Set(id_set));
    let config = CheckerConfig {
        allow_deadlock: true,
        quiet: true,
        spec_path: Some(param_path.to_path_buf()),
        ..CheckerConfig::default()
    };
    let result = check(&param_spec, &env, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 9);
        }
        other => panic!("parameterized_instance should pass, got {:?}", other),
    }

    let pingpong_path = Path::new("test_cases/should_pass/pingpong.tla");
    let pingpong_text =
        std::fs::read_to_string(pingpong_path).expect("failed to read pingpong.tla");
    let pingpong_spec = parse(&pingpong_text).expect("failed to parse pingpong.tla");
    let mut env = Env::new();
    env.insert(Arc::from("NumberOfClients"), Value::Int(1));
    env.insert(Arc::from("NumberOfPings"), Value::Int(1));
    let config = CheckerConfig {
        allow_deadlock: true,
        quiet: true,
        spec_path: Some(pingpong_path.to_path_buf()),
        ..CheckerConfig::default()
    };
    let result = check(&pingpong_spec, &env, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 4);
        }
        other => panic!("pingpong should pass, got {:?}", other),
    }

    let inline_text = include_str!("../test_cases/benchmark/inline_channels.tla");
    let inline_spec = parse(inline_text).expect("failed to parse inline_channels.tla");
    let env = Env::new();
    let config = CheckerConfig {
        allow_deadlock: true,
        quiet: true,
        ..CheckerConfig::default()
    };
    let result = check(&inline_spec, &env, &config);
    match result {
        CheckResult::Ok(stats) => {
            assert_eq!(stats.states_explored, 9);
        }
        other => panic!("inline_channels should pass, got {:?}", other),
    }
}

fn create_test_set(size: usize) -> BTreeSet<Value> {
    (0..size).map(|i| Value::Int(i as i64)).collect()
}

fn create_test_state(var_count: usize, set_size: usize) -> State {
    let values: Vec<Value> = (0..var_count)
        .map(|_| {
            let set: BTreeSet<Value> = (0..set_size).map(|j| Value::Int(j as i64)).collect();
            Value::Set(set)
        })
        .collect();
    State { values }
}

fn bench_eval_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("eval_ops");
    let defs = Definitions::new();
    let env = Env::new();

    for size in [5, 10, 15] {
        let set: BTreeSet<Value> = create_test_set(size);
        let base_expr = Expr::Lit(Value::Set(set));
        let powerset_expr = Expr::Powerset(Box::new(base_expr));

        group.bench_with_input(
            BenchmarkId::new("powerset", size),
            &powerset_expr,
            |b, expr| b.iter(|| eval(black_box(expr), &mut env.clone(), &defs)),
        );
    }

    for set_size in [100, 1000, 10000] {
        let set: BTreeSet<Value> = create_test_set(set_size);
        let elem = Value::Int(set_size as i64 / 2);

        group.bench_with_input(
            BenchmarkId::new("set_membership", set_size),
            &(set.clone(), elem.clone()),
            |b, (s, e)| b.iter(|| black_box(s).contains(black_box(e))),
        );
    }

    for var_count in [5, 10, 20] {
        let state = create_test_state(var_count, 10);

        group.bench_with_input(BenchmarkId::new("state_hash", var_count), &state, |b, s| {
            b.iter(|| {
                let mut hasher = DefaultHasher::new();
                black_box(s).hash(&mut hasher);
                hasher.finish()
            })
        });
    }

    for var_count in [5, 10, 20] {
        let mut env_to_clone = Env::new();
        for i in 0..var_count {
            let set: BTreeSet<Value> = create_test_set(10);
            env_to_clone.insert(Arc::from(format!("var{}", i)), Value::Set(set));
        }

        group.bench_with_input(
            BenchmarkId::new("env_clone", var_count),
            &env_to_clone,
            |b, e| b.iter(|| black_box(e).clone()),
        );
    }

    group.finish();
}

fn bench_symmetry_canonicalize(c: &mut Criterion) {
    let mut group = c.benchmark_group("symmetry");

    let sym_set: BTreeSet<Value> = ["a", "b", "c", "d", "e"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut sym_config = SymmetryConfig::new();
    sym_config.add_symmetric_set(sym_set.clone());

    for var_count in [3, 5, 10] {
        let values: Vec<Value> = (0..var_count)
            .map(|i| {
                let subset: BTreeSet<Value> = sym_set.iter().take((i % 5) + 1).cloned().collect();
                Value::Set(subset)
            })
            .collect();
        let state = State { values };

        group.bench_with_input(
            BenchmarkId::new("canonicalize", var_count),
            &state,
            |b, s| b.iter(|| sym_config.canonicalize(black_box(s))),
        );
    }

    group.finish();
}

fn bench_btreeset_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("btreeset_ops");

    for size in [100, 1000, 10000] {
        let set: BTreeSet<Value> = create_test_set(size);

        group.bench_with_input(BenchmarkId::new("clone", size), &set, |b, s| {
            b.iter(|| black_box(s).clone())
        });

        group.bench_with_input(BenchmarkId::new("insert_new", size), &set, |b, s| {
            b.iter(|| {
                let mut cloned = s.clone();
                cloned.insert(Value::Int(size as i64 + 1));
                cloned
            })
        });

        let other: BTreeSet<Value> = (size / 2..size + size / 2)
            .map(|i| Value::Int(i as i64))
            .collect();

        group.bench_with_input(
            BenchmarkId::new("union", size),
            &(set.clone(), other),
            |b, (s, o)| {
                b.iter(|| {
                    black_box(s)
                        .union(black_box(o))
                        .cloned()
                        .collect::<BTreeSet<_>>()
                })
            },
        );
    }

    group.finish();
}

fn bench_state_indexset(c: &mut Criterion) {
    use indexmap::IndexSet;

    let mut group = c.benchmark_group("state_indexset");

    for state_count in [100, 1000, 5000] {
        let states: Vec<State> = (0..state_count)
            .map(|i| State {
                values: vec![Value::Int(i as i64), Value::Int((i * 2) as i64)],
            })
            .collect();

        group.bench_with_input(
            BenchmarkId::new("build_set", state_count),
            &states,
            |b, states| {
                b.iter(|| {
                    let mut set = IndexSet::new();
                    for s in states {
                        set.insert(s.clone());
                    }
                    set
                })
            },
        );

        let mut existing_set: IndexSet<State> = IndexSet::new();
        for s in &states {
            existing_set.insert(s.clone());
        }
        let lookup_state = states[state_count / 2].clone();

        group.bench_with_input(
            BenchmarkId::new("lookup", state_count),
            &(existing_set, lookup_state),
            |b, (set, state)| b.iter(|| black_box(set).contains(black_box(state))),
        );
    }

    group.finish();
}

fn bench_twophase(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/official/TwoPhase.tla");
    let spec = parse(spec_text).expect("failed to parse TwoPhase.tla");

    let mut group = c.benchmark_group("twophase");

    for rm_count in [3, 4, 5] {
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

fn bench_enabled(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/benchmark/enabled_bench.tla");
    let spec = parse(spec_text).expect("failed to parse enabled_bench.tla");

    let env = Env::new();
    let mut group = c.benchmark_group("enabled");

    group.bench_function("enabled_bench", |b| {
        b.iter(|| {
            let config = quiet_config();
            check(&spec, &env, &config)
        });
    });

    group.finish();
}

fn bench_queens(c: &mut Criterion) {
    let spec_text = include_str!("../test_cases/official/Queens.tla");
    let spec = parse(spec_text).expect("failed to parse Queens.tla");

    let mut env = Env::new();
    env.insert(Arc::from("N"), Value::Int(4));

    let mut group = c.benchmark_group("queens");

    group.bench_function("n4", |b| {
        b.iter(|| {
            let config = CheckerConfig {
                allow_deadlock: true,
                ..quiet_config()
            };
            check(&spec, &env, &config)
        });
    });

    group.finish();
}

fn bench_parameterized_instance(c: &mut Criterion) {
    let path = Path::new("test_cases/should_pass/parameterized_instance.tla");
    let spec_text =
        std::fs::read_to_string(path).expect("failed to read parameterized_instance.tla");
    let spec = parse(&spec_text).expect("failed to parse parameterized_instance.tla");

    let mut group = c.benchmark_group("parameterized_instance");

    let configs: &[(&[&str], &str)] = &[
        (&["a"], "1_channel"),
        (&["a", "b"], "2_channels"),
        (&["a", "b", "c"], "3_channels"),
    ];

    for (ids, label) in configs {
        let id_set: BTreeSet<Value> = ids.iter().map(|s| Value::Str(Arc::from(*s))).collect();
        let mut env = Env::new();
        env.insert(Arc::from("Ids"), Value::Set(id_set));

        group.bench_with_input(BenchmarkId::new("ids", label), &env, |b, env| {
            b.iter(|| {
                let config = CheckerConfig {
                    allow_deadlock: true,
                    spec_path: Some(path.to_path_buf()),
                    ..quiet_config()
                };
                check(&spec, env, &config)
            });
        });
    }
    group.finish();
}

fn bench_pingpong(c: &mut Criterion) {
    let path = Path::new("test_cases/should_pass/pingpong.tla");
    let spec_text = std::fs::read_to_string(path).expect("failed to read pingpong.tla");
    let spec = parse(&spec_text).expect("failed to parse pingpong.tla");

    let mut group = c.benchmark_group("pingpong");

    for (clients, pings) in [(1, 1), (2, 1), (2, 2)] {
        let mut env = Env::new();
        env.insert(Arc::from("NumberOfClients"), Value::Int(clients));
        env.insert(Arc::from("NumberOfPings"), Value::Int(pings));

        group.bench_with_input(
            BenchmarkId::new("clients_pings", format!("{clients}c_{pings}p")),
            &env,
            |b, env| {
                b.iter(|| {
                    let config = CheckerConfig {
                        allow_deadlock: true,
                        spec_path: Some(path.to_path_buf()),
                        ..quiet_config()
                    };
                    check(&spec, env, &config)
                });
            },
        );
    }
    group.finish();
}

fn bench_instance_overhead(c: &mut Criterion) {
    let instance_path = Path::new("test_cases/should_pass/parameterized_instance.tla");
    let instance_text =
        std::fs::read_to_string(instance_path).expect("failed to read parameterized_instance.tla");
    let instance_spec = parse(&instance_text).expect("failed to parse parameterized_instance.tla");

    let inline_text = include_str!("../test_cases/benchmark/inline_channels.tla");
    let inline_spec = parse(inline_text).expect("failed to parse inline_channels.tla");

    let id_set: BTreeSet<Value> = ["a", "b"]
        .iter()
        .map(|s| Value::Str(Arc::from(*s)))
        .collect();

    let mut instance_env = Env::new();
    instance_env.insert(Arc::from("Ids"), Value::Set(id_set));

    let inline_env = Env::new();

    let mut group = c.benchmark_group("instance_overhead");

    group.bench_function("inline_2ch", |b| {
        b.iter(|| {
            let config = CheckerConfig {
                allow_deadlock: true,
                ..quiet_config()
            };
            check(&inline_spec, &inline_env, &config)
        });
    });

    group.bench_function("instance_2ch", |b| {
        b.iter(|| {
            let config = CheckerConfig {
                allow_deadlock: true,
                spec_path: Some(instance_path.to_path_buf()),
                ..quiet_config()
            };
            check(&instance_spec, &instance_env, &config)
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_large_counter,
    bench_symmetric_procs,
    bench_diehard,
    bench_tcommit,
    bench_twophase,
    bench_enabled,
    bench_queens,
    bench_eval_operations,
    bench_symmetry_canonicalize,
    bench_btreeset_operations,
    bench_state_indexset,
    bench_parameterized_instance,
    bench_pingpong,
    bench_instance_overhead,
);

criterion_main!(benches);

#[test]
fn test_benchmarks_validity() {
    validate_benchmarks();
}
