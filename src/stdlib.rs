use std::collections::BTreeSet;
use std::sync::Arc;

use crate::ast::{Env, Value};

pub fn load_builtins(env: &mut Env) {
    let boolean: BTreeSet<Value> = [Value::Bool(false), Value::Bool(true)]
        .into_iter()
        .collect();
    env.insert(Arc::from("BOOLEAN"), Value::Set(boolean));
}

pub fn load_module(name: &str, env: &mut Env) {
    match name {
        "Naturals" => load_naturals(env),
        "Integers" => load_integers(env),
        "Sequences" => load_sequences(env),
        "FiniteSets" => load_finitesets(env),
        "TLC" => load_tlc(env),
        "Bags" => load_bags(env),
        "Bits" => {}
        _ => {}
    }
}

fn load_naturals(env: &mut Env) {
    let nat: BTreeSet<Value> = (0..=100).map(Value::Int).collect();
    env.insert(Arc::from("Nat"), Value::Set(nat));
}

fn load_integers(env: &mut Env) {
    load_naturals(env);
    let int: BTreeSet<Value> = (-100..=100).map(Value::Int).collect();
    env.insert(Arc::from("Int"), Value::Set(int));
}

fn load_sequences(_env: &mut Env) {}

fn load_finitesets(_env: &mut Env) {}

fn load_tlc(_env: &mut Env) {}

fn load_bags(_env: &mut Env) {}
