use std::collections::BTreeMap;
use std::sync::Arc;

use crate::ast::{State, Value};

pub(super) fn value_to_json(v: &Value) -> serde_json::Value {
    match v {
        Value::Bool(b) => serde_json::Value::Bool(*b),
        Value::Int(n) => serde_json::Value::Number((*n).into()),
        Value::Str(s) => serde_json::Value::String(s.to_string()),
        Value::Set(set) => serde_json::Value::Array(set.iter().map(value_to_json).collect()),
        Value::Fn(map) => {
            let entries: Vec<serde_json::Value> = map
                .iter()
                .map(|(k, v)| serde_json::json!([value_to_json(k), value_to_json(v)]))
                .collect();
            serde_json::json!({"__fn": entries})
        }
        Value::Record(fields) => {
            let obj: serde_json::Map<String, serde_json::Value> = fields
                .iter()
                .map(|(k, v)| (k.to_string(), value_to_json(v)))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Tuple(elems) => {
            serde_json::json!({"__tuple": elems.iter().map(value_to_json).collect::<Vec<_>>()})
        }
    }
}

pub(super) fn json_to_value(j: &serde_json::Value) -> Option<Value> {
    match j {
        serde_json::Value::Bool(b) => Some(Value::Bool(*b)),
        serde_json::Value::Number(n) => Some(Value::Int(n.as_i64()?)),
        serde_json::Value::String(s) => Some(Value::Str(Arc::from(s.as_str()))),
        serde_json::Value::Array(arr) => {
            let set: std::collections::BTreeSet<Value> =
                arr.iter().filter_map(json_to_value).collect();
            Some(Value::Set(set))
        }
        serde_json::Value::Object(obj) => {
            if let Some(fn_arr) = obj.get("__fn") {
                let entries = fn_arr.as_array()?;
                let map: BTreeMap<Value, Value> = entries
                    .iter()
                    .filter_map(|e| {
                        let arr = e.as_array()?;
                        let k = json_to_value(arr.first()?)?;
                        let v = json_to_value(arr.get(1)?)?;
                        Some((k, v))
                    })
                    .collect();
                return Some(Value::Fn(map));
            }
            if let Some(tuple_arr) = obj.get("__tuple") {
                let elems: Vec<Value> = tuple_arr
                    .as_array()?
                    .iter()
                    .filter_map(json_to_value)
                    .collect();
                return Some(Value::Tuple(elems));
            }
            let fields: BTreeMap<Arc<str>, Value> = obj
                .iter()
                .filter_map(|(k, v)| Some((Arc::from(k.as_str()), json_to_value(v)?)))
                .collect();
            Some(Value::Record(fields))
        }
        serde_json::Value::Null => None,
    }
}

pub(super) fn state_to_json(state: &State, vars: &[Arc<str>]) -> serde_json::Value {
    let obj: serde_json::Map<String, serde_json::Value> = vars
        .iter()
        .enumerate()
        .filter_map(|(i, var)| {
            let val = state.values.get(i)?;
            Some((var.to_string(), value_to_json(val)))
        })
        .collect();
    serde_json::Value::Object(obj)
}

pub(super) fn json_to_state(j: &serde_json::Value, vars: &[Arc<str>]) -> Option<State> {
    let obj = j.as_object()?;
    let values: Vec<Value> = vars
        .iter()
        .map(|var| {
            obj.get(var.as_ref())
                .and_then(json_to_value)
                .unwrap_or(Value::Bool(false))
        })
        .collect();
    Some(State { values })
}
