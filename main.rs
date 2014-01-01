use std::hashmap::HashMap;

#[deriving(Clone)]
#[deriving(Eq)]
#[deriving(ToStr)]
enum Type {
    Variable(int),
    Operator(~str, ~[Type])
}

struct TypedExpr {
    expr : Expr<~TypedExpr>,
    typ : @mut Type
}

impl TypedExpr {
    fn new(expr : Expr<~TypedExpr>) -> TypedExpr {
        TypedExpr { expr : expr, typ : @mut Variable(0) }
    }
}

enum Expr<T> {
    Identifier(~str),
    Apply(T, T),
    Number(int),
    Lambda(~str, T),
    Let(~[(~str, T)], T)
}

enum Instruction {
    Add,
    Sub,
    Push(int),
    PushGlobal(int),
    PushInt(int),
    Mkap,
    Eval,
    Unwind,
    Slide(int),
}

enum Var {
    StackVariable(int),
    GlobalVariable(int)
}

struct SuperCombinator {
    arity : int,
    instructions : ~[Instruction]
}
impl SuperCombinator {
    fn new() -> SuperCombinator {
        SuperCombinator { arity : 0, instructions : ~[] }
    }
}

struct Scope {
    variables : HashMap<~str, Var>
}

struct ScopedLookup {
    scopes : ~[Scope],
}

impl ScopedLookup {
    fn new_scope(&mut self, scope : Scope) {
        self.scopes.push(scope);
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn find(&self, identifier : &str) -> Option<Var> {
        for scope in self.scopes.rev_iter() {
           match scope.variables.find_equiv(&identifier) {
                Some(var) => { return Some(*var); }
                None => {}
           }
        }
        return None
    }
}

struct Compiler {
    stackSize : int,
    globals : HashMap<~str, SuperCombinator>,
    variables : HashMap<~str, Var>,
    globalIndex : int
}

impl Compiler {
    fn compileBinding(&mut self, identifier : ~str, expr : &TypedExpr) {
        self.variables.insert(identifier.clone(), GlobalVariable(self.globalIndex));
        self.globalIndex += 1;

        let mut comb = SuperCombinator::new();
        match &expr.expr {
            &Lambda(_, _) => {
                
            }
            _ => self.compile(expr, &mut comb.instructions)
       }
       self.globals.insert(identifier, comb);
    }

    fn compile(&mut self, expr : &TypedExpr, instructions : &mut ~[Instruction]) {
        match &expr.expr {
            &Identifier(ref name) => {
                match self.variables.find(name) {
                    None => fail!("Undefined variable " + *name),
                    Some(var) => {
                        match var {
                            &StackVariable(index) => instructions.push(Push(index)),
                            &GlobalVariable(index) => instructions.push(PushGlobal(index))
                        }
                    }
                }
            }
            &Number(num) => instructions.push(PushInt(num)),
            &Apply(ref func, ref arg) => {
                self.compile(*arg, instructions);
                self.compile(*func, instructions);
                instructions.push(Mkap);
                instructions.push(Eval);
            }
            &Lambda(_, _) => {
                fail!("Can't compile a lambda");
            }
            &Let(ref bindings, ref body) => {
                for &(ref name, ref expr) in bindings.iter() {
                    self.variables.insert(name.clone(), StackVariable(self.stackSize));
                    self.stackSize += 1;
                    self.compile(*expr, instructions);
                }
                self.compile(*body, instructions);
                instructions.push(Slide(bindings.len() as int));
                self.stackSize -= bindings.len() as int;
            }
        }
    }
}

struct TypeEnvironment<'self> {
    namedTypes : HashMap<~str, @mut Type>,
    types : ~[@mut Type],
    variableIndex : int
}

impl TypeEnvironment {
    fn new() -> TypeEnvironment {
        TypeEnvironment { namedTypes : HashMap::new(), types : ~[] , variableIndex : 0 }
    }

    fn replace(old : &mut Type, subs : &HashMap<int, Type>) {
        match old {
            &Variable(id) => {
                match subs.find(&id) {
                    Some(new) => { *old = new.clone() }
                    None => ()
                }
            }
            &Operator(_, ref mut oldTypes) => {
                for t in oldTypes.mut_iter() {
                    TypeEnvironment::replace(t, subs); 
                }
            }
        }
    }

    fn typecheck(&mut self, expr : &mut TypedExpr) {
        *expr.typ = Variable(self.variableIndex);
        self.variableIndex += 1;
        self.types.push(expr.typ);
        match &mut expr.expr {
            &Number(_) => {
                expr.typ = @mut Operator(~"Int", ~[]);
            }
            &Identifier(ref name) => {
                match self.namedTypes.find(name) {
                    Some(t) => { expr.typ = (*t).clone(); }
                    None => { fail!("Undefined identifier " + *name); }
                }
            }
            &Apply(ref mut func, ref mut arg) => {
                println!("Applying");
                self.typecheck(*func);
                self.typecheck(*arg);
                let mut funcType = Operator(~"->", ~[(*arg.typ).clone(), Variable(self.variableIndex)]);
                self.variableIndex += 1;
                let subs = unify(self, func.typ, &funcType);
                self.substitute(&subs);
                TypeEnvironment::replace(&mut funcType, &subs);
                *expr.typ = match funcType {
                    Operator(_, t) => t[1],
                    _ => fail!("Can't happen")
                };
            }
            _ => { () }
        };
    }

    fn substitute(&mut self, subs : &HashMap<int, Type>) {
        //println!("Substituting {:?}", subs);
        for t in self.types.iter() {
            println!("Type : {:?}", *t);
            TypeEnvironment::replace(*t, subs);
        }
    }

    fn addName(&mut self, name : ~str, t : @mut Type) {
        self.namedTypes.insert(name, t);
        self.addType(t);
    }

    fn addType(&mut self, t : @mut Type) {
        self.types.push(t);
    }
}

fn unify(env : &mut TypeEnvironment, lhs : &Type, rhs : &Type) -> HashMap<int, Type> {
    let mut subs = HashMap::new();
    unify_(env, &mut subs, lhs, rhs);
    subs
}
fn unify_(env : &mut TypeEnvironment, subs : &mut HashMap<int, Type>, lhs : &Type, rhs : &Type) {
    
    //println!("Unifying {:?} and {:?}", lhs, rhs);
    match (lhs, rhs) {
        (&Variable(lid), &Variable(rid)) => {
            if lid != rid {
                subs.insert(lid, Variable(rid));
            }
        }
        (&Operator(ref lName, ref lTypes), &Operator(ref rName, ref rTypes)) => {
            if *lName != *rName || lTypes.len() != rTypes.len() {
                fail!("Could not unify Operators " + *lName + " and " + *rName);
            }
            for i in range(0, lTypes.len()) {
                unify_(env, subs, &lTypes[i], &rTypes[i]);
            }
        }
        (&Variable(lid), &Operator(_, _)) => { subs.insert(lid, (*rhs).clone()); }
        _ => { unify_(env, subs, rhs, lhs); }
    }
}

fn function_type(func : &Type, arg : &Type) -> Type {
    Operator(~"->", ~[func.clone(), arg.clone()])
}

#[deriving(Clone)]
enum Node {
    Application(@Node, @Node),
    Int(int),
    Combinator(@SuperCombinator)
}

struct VM {
    globals : ~[@SuperCombinator],
    heap : ~[Node]
}

impl VM {
    fn new() -> VM {
        VM { globals : ~[], heap : ~[] }
    }
    fn execute(&self, stack : &mut ~[@Node], code : &[Instruction]) {
        debug!("Entering frame");
        let mut i = 0;
        while i < code.len() {
            println!("Executing instruction : {:?}", code[i]);
            match &code[i] {
                &Add => {
                    let l = stack.pop();
                    let r = stack.pop();
                    println!("{:?} + {:?}", l, r);
                    match (*l, *r) {
                        (Int(lhs), Int(rhs)) => { stack.push(@Int(lhs + rhs)); }
                        _ => fail!("Expected fully evaluted numbers in Add instruction")
                    }
                }
                &Sub => {
                    let l = stack.pop();
                    let r = stack.pop();
                    match (*l, *r) {
                        (Int(lhs), Int(rhs)) => { stack.push(@Int(lhs - rhs)); }
                        _ => fail!("Expected fully evaluted numbers in Sub instruction")
                    }
                }
                &PushInt(value) => { stack.push(@Int(value)); }
                &Push(index) => {
                    let x = stack[index].clone();
                    stack.push(x);
                }
                &PushGlobal(index) => {
                    stack.push(@Combinator(self.globals[index]));
                }
                &Mkap => {
                    let func = stack.pop();
                    let arg = stack.pop();
                    stack.push(@Application(func, arg));
                }
                &Eval => {
                    static unwindCode : &'static [Instruction] = &[Unwind];
                    let mut newStack = ~[stack[stack.len() - 1]];
                    self.execute(&mut newStack, unwindCode);
                    assert!(newStack.len() == 1);
                    stack[stack.len() - 1] = newStack[0];
                }
                &Unwind => {
                    match *stack[stack.len() - 1] {
                        Application(func, arg) => {
                            stack.push(func);
                            i -= 1;//Redo the unwind instruction
                        }
                        Combinator(comb) => {
                            for j in range(stack.len() - (comb.arity as uint) - 1, stack.len()) {
                                stack[j] = match stack[j] {
                                    @Application(func, arg) => arg,
                                    _ => fail!("Expected Application")
                                };
                            }
                            let mut newStack = ~[stack[stack.len() - 1]];
                            self.execute(&mut newStack, comb.instructions);
                            assert!(newStack.len() == 0);
                            for i in range(0, comb.arity) {
                                stack.pop();
                            }
                            stack.push(newStack[0]);
                        }
                        Int(_) => ()
                    }
                }
                &Slide(size) => {
                    for _ in range(0, size) {
                        stack.pop();
                    }
                }
            }
            i += 1;
        }
    }
}

fn main() {
    let t1 = @mut Variable(1);
    let t2 = @mut Operator(~"->", ~[Variable(1), Operator(~"Int", ~[])]);
    let mut env = TypeEnvironment::new();
    env.addType(t1);
    env.addType(t2);
    let n = ~TypedExpr::new(Identifier(~"add"));
    let num = ~TypedExpr::new(Number(1));
    let mut expr = TypedExpr::new(Apply(n, num));
    let type_int = Operator(~"Int", ~[]);
    let add_type = @mut function_type(&type_int, &function_type(&type_int, &type_int));
    env.addName(~"add", add_type);
    env.typecheck(&mut expr);

    println!("Result {:?}", expr.typ);


    let instr = [PushInt(2), PushInt(3), Add];
    let vm = VM::new();
    let mut stack = ~[];
    vm.execute(&mut stack, instr);

    println!("Add : {:?}", stack);

}


