use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet, FxHasher};
use smartstring::alias::String;
use std::fmt::Debug;
use std::fmt::Write;
use std::hash::{Hash, Hasher};
use std::path::PathBuf;
use std::process::exit;
use std::{cell::RefCell, iter::zip, rc::Rc};

use pest::error::{Error, LineColLocation};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;

#[cfg(not(target_env = "msvc"))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

#[derive(Parser)]
#[grammar = "weldfile.pest"]
pub struct WeldFileParser {
    // pratt_parser: PrattParser<Rule>,
}

struct Context {
    verbose: bool,
}

#[allow(dead_code)]
fn destructure1(pair: Pair<'_, Rule>) -> Pair<'_, Rule> {
    let mut inner = pair.into_inner();
    inner.next().unwrap()
}

#[allow(dead_code)]
fn destructure2(pair: Pair<'_, Rule>) -> (Pair<'_, Rule>, Pair<'_, Rule>) {
    let mut inner = pair.into_inner();
    (inner.next().unwrap(), inner.next().unwrap())
}

type Namespace<'a> = Rc<RefCell<HashMap<String, Value<'a>>>>;

#[derive(Clone, Debug)]
struct Func<'a> {
    name: String,
    args: Vec<String>,
    defaults: HashMap<String, Value<'a>>,
    // TODO: pos_spread, named_spread
    context: Vec<Namespace<'a>>,
    body: Pair<'a, Rule>,
}
impl PartialEq for Func<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.body.line_col() == other.body.line_col()
    }
}

#[derive(Clone, Debug)]
struct BuiltinFunc<'a> {
    name: String,
    args: Vec<String>,
    defaults: HashMap<String, Value<'a>>,
    // TODO: pos_spread, named_spread
    body: fn(Vec<Value<'a>>, ctx: &Context) -> Value<'a>,
}

impl PartialEq for BuiltinFunc<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.body as usize == other.body as usize
    }
}

#[derive(Clone, PartialEq)]
enum Value<'a> {
    Int(u64),
    Bool(bool),
    Str(String),
    Dict(Namespace<'a>),
    List(Vec<Value<'a>>),
    Func(Func<'a>),
    BuiltinFunc(BuiltinFunc<'a>),
}

impl<'a> Value<'a> {
    fn as_flat_list(&self) -> Vec<Value<'a>> {
        let mut vec = vec![];
        match self {
            Value::List(list) => {
                for item in list {
                    vec.extend(item.as_flat_list());
                }
            }
            v => {
                vec.push(v.to_owned());
            }
        }
        vec
    }

    fn as_str(&self) -> &str {
        match self {
            Value::Str(s) => s,
            _ => panic!("Expected string, got {:?}", self),
        }
    }
}

impl Debug for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Str(s) => write!(f, "{:?}", s),
            Value::Dict(d) => {
                let d = d.borrow();
                write!(f, "{{")?;
                let mut sorted_keys = d.keys().collect::<Vec<_>>();
                sorted_keys.sort_unstable();
                for (i, k) in sorted_keys.into_iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}={:?}", k, d[k])?;
                }
                write!(f, "}}")
            }
            Value::List(l) => write!(f, "{:?}", l),
            Value::Func(func) => {
                write!(f, "{}(", func.name)?;
                for (i, arg) in func.args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ") {{...}}")
            }
            Value::BuiltinFunc(func) => {
                write!(f, "{}(", func.name)?;
                for (i, arg) in func.args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ") {{builtin}}")
            }
        }
    }
}

fn hash_value(hasher: &mut FxHasher, val: &Value) {
    match val {
        Value::Int(i) => i.hash(hasher),
        Value::Bool(b) => b.hash(hasher),
        Value::Str(s) => s.hash(hasher),
        Value::Dict(d) => {
            let d = d.borrow();
            d.len().hash(hasher);
            for (k, v) in d.iter() {
                k.hash(hasher);
                hash_value(hasher, v);
            }
        }
        Value::List(l) => {
            l.len().hash(hasher);
            for v in l {
                hash_value(hasher, v);
            }
        }
        Value::Func(func) => {
            func.name.hash(hasher);
        }
        Value::BuiltinFunc(func) => {
            func.name.hash(hasher);
        }
    }
}

fn deref<'a>(name: &str, stack: &[Namespace<'a>]) -> Option<Value<'a>> {
    if name == "UNIQUE" {
        let mut hasher = FxHasher::default();
        for ns in stack.iter() {
            let ns = ns.borrow();
            for (k, v) in ns.iter() {
                k.hash(&mut hasher);
                hash_value(&mut hasher, v);
            }
        }
        return Some(Value::Str(format!("{:016x}", hasher.finish()).into()));
    }
    for ns in stack.iter().rev() {
        if let Some(val) = ns.borrow().get(name) {
            return Some(val.to_owned());
        }
    }
    None
}

fn eval<'a>(pair: Pair<'a, Rule>, stack: &mut Vec<Namespace<'a>>, ctx: &Context) -> Value<'a> {
    match pair.as_rule() {
        Rule::expr => {
            let mut inner = pair.into_inner();
            let inner_expr = inner.next().unwrap();
            // if inner_expr.as_rule() == Rule::expr {
            //     return eval(inner_expr, stack);
            // }
            let mut inner_val = eval(destructure1(inner_expr), stack, ctx);
            for expr_modifier in inner {
                match expr_modifier.as_rule() {
                    Rule::member_access => {
                        let member_name = expr_modifier.into_inner().next().unwrap().as_str();
                        if let Value::Dict(dict) = inner_val {
                            inner_val = deref(member_name, &[dict.clone()]).unwrap_or_else(|| {
                                panic!("Unknown member: {} of {:?}", member_name, dict)
                            });
                        } else {
                            panic!("Tried to access member of non dict: {:?}", inner_val);
                        }
                    }
                    Rule::func_call => {
                        let inner = expr_modifier.into_inner();
                        let pos_args = inner.map(|expr| eval(expr, stack, ctx)).collect::<Vec<_>>();
                        match inner_val {
                            Value::Func(func) => inner_val = call_func(func, pos_args, ctx),
                            Value::BuiltinFunc(func) => inner_val = (func.body)(pos_args, ctx),
                            _ => {
                                panic!("Tried to call non function: {:?}", inner_val);
                            }
                        }
                    }
                    Rule::op_add => {
                        let rhs = eval(expr_modifier.into_inner().next().unwrap(), stack, ctx);
                        inner_val = match (inner_val, rhs) {
                            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
                            (Value::Str(lhs), Value::Str(rhs)) => Value::Str(lhs + &rhs),
                            (Value::List(lhs), Value::List(rhs)) => {
                                Value::List([lhs, rhs].concat())
                            }
                            (lhs, rhs) => panic!("Cannot add {:?} and {:?}", lhs, rhs),
                        };
                    }
                    Rule::op_mul => {
                        let rhs = eval(expr_modifier.into_inner().next().unwrap(), stack, ctx);
                        inner_val = match (inner_val, rhs) {
                            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs * rhs),
                            (Value::Str(lhs), Value::Int(rhs)) => {
                                Value::Str(lhs.repeat(rhs as usize).into())
                            }
                            (lhs, rhs) => panic!("Cannot multiply {:?} and {:?}", lhs, rhs),
                        };
                    }
                    _ => unreachable!("{:#?}", expr_modifier),
                }
            }
            inner_val
        }
        // Rule::expr => eval(destructure1(pair), stack),
        Rule::int_literal => Value::Int(pair.as_str().parse::<u64>().unwrap()),
        Rule::bool_literal => Value::Bool(pair.as_str() == "true"),
        Rule::string_literal => {
            let pair_str = pair.as_str();
            Value::Str(pair_str[1..pair_str.len() - 1].into())
        }
        Rule::list_literal => {
            Value::List(pair.into_inner().map(|tok| eval(tok, stack, ctx)).collect())
        }
        Rule::dict_literal => {
            stack.push(Default::default());
            for dict_item in pair.into_inner() {
                match dict_item.as_rule() {
                    Rule::assignment => make_assignment(dict_item, stack, ctx),
                    Rule::func_def => make_func_def(dict_item, stack),
                    Rule::COMMENT => {}
                    _ => unreachable!("{:#?}", dict_item),
                }
            }
            Value::Dict(stack.pop().unwrap())
        }
        Rule::ident => {
            let ident = pair.as_str();
            deref(ident, stack).unwrap_or_else(|| panic!("Unknown variable: {}", ident))
        }
        _ => unreachable!("{:#?}", pair),
    }
}

fn call_func<'a>(func: Func<'a>, pos_args: Vec<Value<'a>>, ctx: &Context) -> Value<'a> {
    let mut args_ns = HashMap::default();
    for (arg_name, arg_val) in zip(func.args.iter(), pos_args) {
        args_ns.insert(arg_name.to_owned(), arg_val);
    }
    let mut new_stack = func.context.clone();
    new_stack.push(Rc::new(RefCell::new(args_ns)));
    let res = eval(func.body.clone(), &mut new_stack, ctx);
    if let Value::Dict(res) = &res {
        res.borrow_mut()
            .entry("_type".into())
            .or_insert_with(|| Value::Str(func.name.clone()));
    }
    res
}

fn builtin_map<'a>(args: Vec<Value<'a>>, ctx: &Context) -> Value<'a> {
    let mut args = args.into_iter();
    if args.len() != 2 {
        panic!("Expected 2 arguments, got {:?}", args);
    }
    let func = match args.next().unwrap() {
        Value::Func(func) => func,
        func => panic!("Expected function, got {:?}", func),
    };
    let list = match args.next().unwrap() {
        Value::List(list) => list,
        list => panic!("Expected list, got {:?}", list),
    };
    let mut res = vec![];
    for item in list {
        res.push(call_func(func.clone(), vec![item], ctx));
    }
    Value::List(res)
}

fn builtin_rule_input<'a>(args: Vec<Value<'a>>, _ctx: &Context) -> Value<'a> {
    let mut args = args.into_iter();
    if args.len() != 1 {
        panic!("Expected 1 argument, got {:?}", args);
    }
    let path = args.next().unwrap();
    let mut dict = HashMap::default();
    dict.insert("path".into(), path);
    dict.insert("_type".into(), Value::Str("In".into()));
    Value::Dict(Rc::new(RefCell::new(dict)))
}

fn builtin_rule_output<'a>(args: Vec<Value<'a>>, _ctx: &Context) -> Value<'a> {
    let mut args = args.into_iter();
    if args.len() != 1 {
        panic!("Expected 1 argument, got {:?}", args);
    }
    let path = args.next().unwrap();
    let mut dict = HashMap::default();
    dict.insert("path".into(), path);
    dict.insert("_type".into(), Value::Str("Out".into()));
    Value::Dict(Rc::new(RefCell::new(dict)))
}

fn builtin_rule_command<'a>(args: Vec<Value<'a>>, _ctx: &Context) -> Value<'a> {
    let mut args = args.into_iter();
    if args.len() != 1 {
        panic!("Expected 1 argument, got {:?}", args);
    }
    let cmd = args.next().unwrap();
    let mut dict = HashMap::default();
    dict.insert("args".into(), cmd);
    dict.insert("_type".into(), Value::Str("Command".into()));
    Value::Dict(Rc::new(RefCell::new(dict)))
}

fn builtin_rule<'a>(args: Vec<Value<'a>>, _ctx: &Context) -> Value<'a> {
    let mut args = args.into_iter();
    if args.len() < 1 || args.len() > 4 {
        panic!("Expected 1 to 4 arguments, got {:?}", args);
    }
    let cmds = args.next().unwrap();
    let mut dict = HashMap::default();
    dict.insert("commands".into(), cmds);
    dict.insert(
        "name".into(),
        args.next().unwrap_or_else(|| Value::Str("".into())),
    );
    dict.insert(
        "inputs".into(),
        args.next().unwrap_or_else(|| Value::List(vec![])),
    );
    dict.insert(
        "outputs".into(),
        args.next().unwrap_or_else(|| Value::List(vec![])),
    );
    dict.insert("_type".into(), Value::Str("Rule".into()));
    Value::Dict(Rc::new(RefCell::new(dict)))
}

fn main() {
    let ctx = Context { verbose: false };

    const PATH: &str = "examples/hello.weld";
    let src = std::fs::read_to_string(PATH).unwrap();
    let parsed = WeldFileParser::parse(Rule::module, &src)
        .unwrap_or_else(|e| print_parse_err(&src, e.with_path(PATH)));
    let mut root_ns = HashMap::default();
    root_ns.insert(
        "map".into(),
        Value::BuiltinFunc(BuiltinFunc {
            name: "map".into(),
            args: vec!["func".into(), "list".into()],
            defaults: Default::default(),
            body: builtin_map,
        }),
    );
    root_ns.insert(
        "In".into(),
        Value::BuiltinFunc(BuiltinFunc {
            name: "In".into(),
            args: vec!["path".into()],
            defaults: Default::default(),
            body: builtin_rule_input,
        }),
    );
    root_ns.insert(
        "Out".into(),
        Value::BuiltinFunc(BuiltinFunc {
            name: "Out".into(),
            args: vec!["path".into()],
            defaults: Default::default(),
            body: builtin_rule_output,
        }),
    );
    root_ns.insert(
        "Command".into(),
        Value::BuiltinFunc(BuiltinFunc {
            name: "Command".into(),
            args: vec!["args".into()],
            defaults: Default::default(),
            body: builtin_rule_command,
        }),
    );
    root_ns.insert(
        "Rule".into(),
        Value::BuiltinFunc(BuiltinFunc {
            name: "Rule".into(),
            args: vec![
                "commands".into(),
                "name".into(),
                "inputs".into(),
                "outputs".into(),
            ],
            defaults: Default::default(),
            body: builtin_rule,
        }),
    );

    let mut root_stack: Vec<Namespace> = vec![Rc::new(RefCell::new(root_ns))];
    for dict_item in parsed {
        match dict_item.as_rule() {
            Rule::assignment => make_assignment(dict_item, &mut root_stack, &ctx),
            Rule::func_def => make_func_def(dict_item, &mut root_stack),
            Rule::EOI => {}
            Rule::COMMENT => {}
            _ => unreachable!("{:#?}", dict_item),
        }
    }

    extract_rules(&root_stack);
}

#[derive(Clone, Debug, PartialEq, Hash)]
struct CommandObj {
    args: Vec<String>,
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RuleId(u64);

#[derive(Clone, Debug, PartialEq, Hash)]
struct RuleObj {
    name: String,
    commands: Vec<CommandObj>,
    inputs: Vec<PathBuf>,
    deps: Vec<RuleId>,
    outputs: Vec<PathBuf>,
}

struct RulesVisitor {
    rule_id_counter: u64,
    outputs: HashMap<PathBuf, RuleId>,
    rules: HashMap<RuleId, RuleObj>,
}

impl RulesVisitor {
    fn new() -> Self {
        Self {
            rule_id_counter: 0,
            outputs: Default::default(),
            rules: Default::default(),
        }
    }

    fn visit_rule(&mut self, obj: Value) -> RuleId {
        let (obj, obj_type) = Self::unwrap_dict(obj);
        let obj = obj.borrow();
        match obj_type.as_str() {
            "Rule" => {
                let mut rule = RuleObj {
                    name: obj.get("name").expect("Expected name").as_str().into(),
                    commands: vec![],
                    inputs: vec![],
                    outputs: vec![],
                    deps: vec![],
                };

                // Construct rule object
                for cmd in obj
                    .get("commands")
                    .expect("Expected commands")
                    .as_flat_list()
                {
                    self.visit_command(cmd, &mut rule);
                }
                for inp in obj.get("inputs").expect("Expected inputs").as_flat_list() {
                    rule.inputs.push(inp.as_str().into());
                }
                for out in obj.get("outputs").expect("Expected outputs").as_flat_list() {
                    rule.outputs.push(out.as_str().into());
                }

                // Check if it exists already
                let mut candidates = HashSet::default();
                for out in rule.outputs.iter() {
                    if let Some(rule_id) = self.outputs.get(out) {
                        candidates.insert(*rule_id);
                    }
                }
                if candidates.len() == 1 {
                    let candidate_id = candidates.iter().next().unwrap();
                    let existing_rule = self.rules.get(candidate_id).unwrap();
                    if existing_rule == &rule {
                        return *candidate_id;
                    }
                }

                // Check if it overlaps with existing outputs
                if !candidates.is_empty() {
                    let mut err_msg = format!(
                        "Rule's outputs conflict with existing rule(s): {:#?}\n",
                        rule
                    );
                    for candidate_id in candidates {
                        let existing_rule = self.rules.get(&candidate_id).unwrap();
                        err_msg.push_str(&format!("-> Existing rule: {:#?}\n", existing_rule));
                    }
                    panic!("{}", err_msg);
                }

                // Fill in deps
                for inp in rule.inputs.iter() {
                    if let Some(rule_id) = self.outputs.get(inp) {
                        rule.deps.push(*rule_id);
                    }
                }

                // Insert into global state
                let new_id = RuleId(self.rule_id_counter);
                for out in rule.outputs.iter() {
                    self.outputs
                        .insert(out.clone(), RuleId(self.rule_id_counter));
                }
                self.rules.insert(new_id, rule);
                self.rule_id_counter += 1;

                new_id
            }
            _ => panic!("Unexpected object type: {}", obj_type),
        }
    }

    fn visit_command(&mut self, obj: Value, rule: &mut RuleObj) {
        let (obj, obj_type) = Self::unwrap_dict(obj);
        let obj = obj.borrow();
        match obj_type.as_str() {
            "Command" => {
                let mut cmd = CommandObj { args: vec![] };
                for arg in obj.get("args").expect("Expected args").as_flat_list() {
                    match arg {
                        Value::Str(s) => cmd.args.push(s),
                        Value::Dict(obj) => {
                            let (obj, obj_type) = Self::unwrap_dict(Value::Dict(obj));
                            match obj_type.as_str() {
                                "Rule" => {
                                    let rule_id = self.visit_rule(Value::Dict(obj));
                                    for out in self.rules.get(&rule_id).unwrap().outputs.iter() {
                                        rule.inputs.push(out.to_owned());
                                        cmd.args.push(out.to_str().unwrap().into());
                                    }
                                    rule.deps.push(rule_id);
                                }
                                "In" => {
                                    let obj = obj.borrow();
                                    let path = obj
                                        .get("path")
                                        .expect("Expected path in `In` object")
                                        .as_str();
                                    rule.inputs.push(path.into());
                                    cmd.args.push(path.into());
                                }
                                "Out" => {
                                    let obj = obj.borrow();
                                    let path = obj
                                        .get("path")
                                        .expect("Expected path in `Out` object")
                                        .as_str();
                                    rule.outputs.push(path.into());
                                    cmd.args.push(path.into());
                                }
                                _ => panic!("Unexpected object type: {}", obj_type),
                            }
                        }
                        _ => panic!("Expected string, got {:?}", arg),
                    }
                }
                rule.commands.push(cmd);
            }
            _ => panic!("Unexpected object type: {}", obj_type),
        }
    }

    fn unwrap_dict(obj: Value) -> (Rc<RefCell<HashMap<String, Value>>>, String) {
        // println!("[@] Visiting obj: {:?}", obj);
        let Value::Dict(obj) = obj else {
            panic!("Expected dict, got {:?}", obj);
        };

        let obj_type = {
            let borrowed_obj = obj.borrow();
            let Value::Str(obj_type) = borrowed_obj.get("_type").expect("Unexpected untyped dict")
            else {
                panic!("Expected string in _type");
            };
            obj_type.to_owned()
        };

        (obj, obj_type)
    }
}

fn extract_rules(root_stack: &[Namespace]) {
    let root_ns = root_stack[0].borrow();
    let entry_var = root_ns.get("all").unwrap();
    let mut visitor = RulesVisitor::new();

    for rule in entry_var.as_flat_list() {
        visitor.visit_rule(rule);
    }

    let mut output = "# Autogenerated by the Weld build system, do not edit manually\n".to_string();

    for rule in visitor.rules.values() {
        for (i, out) in rule.outputs.iter().enumerate() {
            if i != 0 {
                output += " ";
            }
            write!(output, "{}", out.to_str().unwrap()).unwrap();
        }
        output += ": ";
        for (i, inp) in rule.inputs.iter().enumerate() {
            if i != 0 {
                output += " ";
            }
            output += inp.to_str().unwrap();
        }
        output += "\n";
        if !rule.name.is_empty() {
            writeln!(output, "    # {}", rule.name).unwrap();
        }
        for cmd in rule.commands.iter() {
            output += "   ";
            for arg in cmd.args.iter() {
                write!(output, " {}", arg).unwrap();
            }
            output += "\n";
        }
    }

    print!("{}", output);

    // let all_var = root_ns.get("all").unwrap();
    // println!("all = {:?}", all_var);
}

fn print_err_with_context(src: &str, line_col: (usize, usize)) {
    let first_ctx_line = (line_col.0 - 1).saturating_sub(1);
    let last_ctx_line = line_col.0 + 1;
    let lines_iter = src
        .lines()
        .skip(first_ctx_line)
        .take(last_ctx_line - first_ctx_line);
    for (i, line) in lines_iter.enumerate() {
        eprintln!("{:>3} | {}", first_ctx_line + i, line);
        if first_ctx_line + i == line_col.0 - 1 {
            eprintln!("    | {}^", " ".repeat(line_col.1 - 1));
        }
    }
}

fn print_parse_err(src: &str, mut err: Error<Rule>) -> ! {
    let line_col = match err.line_col {
        LineColLocation::Pos(p) => p,
        LineColLocation::Span(start, _end) => start,
    };
    let err_path = err.path().unwrap_or("STDIN").to_owned();
    if let pest::error::ErrorVariant::ParsingError {
        positives,
        negatives,
    } = &mut err.variant
    {
        positives.retain(|r| !matches!(r, Rule::COMMENT));
        negatives.retain(|r| !matches!(r, Rule::COMMENT));
    }
    eprintln!(
        "error: {} at {}:{}:{}",
        err.renamed_rules(|r| match r {
            Rule::EOI => "end of input".to_string(),
            Rule::WHITESPACE => "whitespace".to_string(),
            Rule::COMMENT => "comment".to_string(),
            Rule::ident => "identifier".to_string(),
            Rule::int_literal => "integer".to_string(),
            Rule::list_literal => "list".to_string(),
            Rule::dict_item => "dict item".to_string(),
            Rule::dict_literal => "dict".to_string(),
            Rule::assignment => "assignment".to_string(),
            Rule::func_def => "function definition".to_string(),
            Rule::func_call => "function call".to_string(),
            Rule::expr | Rule::raw_expr => "expression".to_string(),
            Rule::sep => "','".to_string(),
            Rule::module => "module".to_string(),
            other => format!("{:?}", other),
        })
        .variant
        .message(),
        err_path,
        line_col.0,
        line_col.1
    );
    print_err_with_context(src, line_col);
    eprintln!();
    exit(1);
}

fn make_assignment<'a>(pair: Pair<'a, Rule>, stack: &mut Vec<Namespace<'a>>, ctx: &Context) {
    let (ident, expr) = destructure2(pair);
    if ctx.verbose {
        println!("[[ {} = {} ]]", ident.as_str(), expr.as_str());
    }
    let res = eval(expr, stack, ctx);
    if ctx.verbose {
        println!(" => {:?}", res);
    }
    stack
        .last()
        .unwrap()
        .borrow_mut()
        .insert(ident.as_str().into(), res);
}

fn make_func_def<'a>(pair: Pair<'a, Rule>, stack: &mut Vec<Namespace<'a>>) {
    let mut inner = pair.into_inner();
    let name = String::from(inner.next().unwrap().as_str());
    let mut arg_names = vec![];
    for pair in inner {
        if pair.as_rule() == Rule::expr {
            // println!("{}({:?}) = {}", name, arg_names, pair.as_str());
            // println!("[[ {} = {} ]]", ident.as_str(), expr.as_str());
            let func = Value::Func(Func {
                name: name.clone(),
                args: arg_names,
                defaults: Default::default(),
                context: stack.clone(),
                body: pair,
            });
            stack.last().unwrap().borrow_mut().insert(name, func);
            break;
        } else if pair.as_rule() == Rule::ident {
            arg_names.push(pair.as_str().into());
        } else {
            unreachable!();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example_val() -> Value<'static> {
        Value::List(vec![
            Value::List(vec![]),
            Value::List(vec![Value::Int(1)]),
            Value::List(vec![Value::Int(2), Value::Int(3)]),
            Value::Int(4),
        ])
    }

    #[test]
    fn test_value_as_flat_list_iter() {
        let list = example_val();
        let mut iter = list.as_flat_list().into_iter();
        assert_eq!(iter.next(), Some(Value::Int(1)));
        assert_eq!(iter.next(), Some(Value::Int(2)));
        assert_eq!(iter.next(), Some(Value::Int(3)));
        assert_eq!(iter.next(), Some(Value::Int(4)));
        assert_eq!(iter.next(), None);
    }
}
