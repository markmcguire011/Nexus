open HashTable;
exception CannotFindIt;
use "exceptions.sml";

datatype value =
  VNUM of int
  | VBOOL of bool
  | VSTR of string
  | VCLOS of closure
  | VOBJ of object
  | VMETHOD of {close: closure, this: object}
  | VN

withtype state = ((string, value) hash_table) list
and classPrototype = (string, value) hash_table
and closure = {func: function, environment: state, id: unit ref}
and object = {obj_hash: classPrototype, id: unit ref}

type classTable = (string, classPrototype) hash_table

val hash_fn : string -> word = HashString.hashString;
val cmp_fn : string * string -> bool = (op =);
val initial_size : int = 101;
val stateTbl : (string, value) hash_table = mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt);


fun findType (v : value) : string =
  case v of
  VNUM x => "number"
  | VBOOL x => "boolean"
  | VSTR x => "string"
  | VCLOS x => "function"
  | VOBJ x => "object"
  | VMETHOD x => "method"
  | VN => "none"
;

fun initializeGlobalVars (decls: string list) : state =
  case decls of
  [] => [mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt)]
  | x::xs => 
    let val tbl = initializeGlobalVars xs in
      case find (hd tbl) x of
      NONE => (insert (hd tbl) (x, VN); tbl)
      | SOME y => raise VariableRedeclarationException x
    end
;

fun initializeFunctionVars (ids: decl list, environment: state) : state = 
  case ids of
  [] => environment
  | x::xs => 
    let val tbl = initializeFunctionVars (xs, environment) in
      case find (hd tbl) x of
      NONE => (insert (hd tbl) (x, VN); tbl)
      | SOME y => raise VariableRedeclarationException x
    end
;

fun initializeFunctions (func_decls : (string * function) list, curState : state) : state = 
  case func_decls of
  [] => curState
  | (fId, func)::xs => 
    let val tbl = initializeFunctions (xs, curState) in
      case find (hd tbl) fId of
      NONE => (insert (hd tbl) (fId, VCLOS {func = func, environment = curState, id = ref ()}); tbl)
      | SOME y => raise VariableRedeclarationException fId
    end
;

fun insertThis (this: object, curState: state) : state =
  (
    insert ((hd curState)) ("this", VOBJ this);
    curState
  )
;

fun createClassPrototype (className: string, decls : decl list, super: string option, funcs : (string * function) list, curState : state, curClassTable : classTable) : classPrototype = 
  let
    val tbl = 
      (case super of 
      SOME superName => 
        (case find curClassTable superName of
        SOME superTbl => copy superTbl
        | NONE => raise UnknownSuperException (className, superName))
      | NONE => mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt))
    val superAttributes = 
      (case super of
      SOME superName =>
        (case find curClassTable superName of
        SOME superTbl => List.map (fn (k,_) => k) (listItemsi superTbl)
        | NONE => [])
      | NONE => [])
    val declMappings = List.map (fn d => (d, VN)) decls
    val funcMappings = List.map (fn (name, func) => 
      (name, VCLOS {func = func, environment = curState, id = ref ()})) funcs
    val allAttributes = declMappings @ funcMappings
  in
    List.app (fn (name, value) => 
      case find tbl name of
      SOME x => 
        (case List.find (fn f => f = name) superAttributes of
        SOME decalredSuper => insert tbl (name, value)
        | NONE => raise VariableRedeclarationException name)
      | NONE => insert tbl (name, value)) allAttributes;
    tbl
  end
;

fun initializeClasses (classes : class list, curState : state) : classTable = 
  case List.rev classes of
  [] => mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt)
  | x::xs => 
    let 
      val {name, super, decls, funcs} = x 
      val tbl = initializeClasses (List.rev xs, curState)
    in
      case find tbl name of
      NONE => (insert tbl (name, createClassPrototype(name, decls, super, funcs, curState, tbl)); tbl)
      | SOME y => raise ClassRedeclarationException name
    end
;

fun assignVar (id : string, res : value, curState : state) : value =
  case curState of 
    [] => raise UndeclaredVariableAssignmentException id
    | y::ys => (case find y id of
      NONE => assignVar (id, res, ys)
      | SOME v => (insert y (id, res); res))
;

fun bindParameters (ids: decl list, vals: value list) : (string, value) hash_table =
  case (ids, vals) of
  ([], []) => mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt)
  | ([], _) => raise CallTooManyArgumentsException
  | (_, []) => raise CallTooFewArgumentsException
  | (x::xs, y::ys) => 
    let val tbl = bindParameters (xs, ys) in
      case find tbl x of
      NONE => (insert tbl (x, y); tbl)
      | SOME y => raise VariableRedeclarationException x
    end
;

fun evalBinary (bexp : {opr: binaryOperator, lft: expression, rht: expression}, curState : state, curClassTable : classTable) : value =
 let val {opr, lft, rht} = bexp in
    case opr of
    BOP_PLUS => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VNUM (num1 + num2)
        | (VSTR str1, VSTR str2) => VSTR (str1 ^ str2)
        | (x, y) => raise AddException (findType x, findType y))

    | BOP_MINUS => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VNUM (num1 - num2)
        | (x, y) => raise ArithmeticException (opr, findType x, findType y))

    | BOP_TIMES =>
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VNUM (num1 * num2)
        | (x, y) => raise ArithmeticException (opr, findType x, findType y))

    | BOP_DIVIDE => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VNUM (num1 div num2)
        | (x, y) => raise ArithmeticException (opr, findType x, findType y))

    | BOP_MOD => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VNUM (num1 mod num2)
        | (x, y) => raise ArithmeticException (opr, findType x, findType y))

    | BOP_EQ => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 = num2)
        | (VSTR str1, VSTR str2) => VBOOL (str1 = str2)
        | (VBOOL bool1, VBOOL bool2) => VBOOL (bool1 = bool2)
        | (VN, VN) => VBOOL (true)
        | (VCLOS {func = func1, environment = environment1, id = id1}, VCLOS{func = func2, environment = environment2, id = id2}) => VBOOL (id1 = id2)
        | (VOBJ {obj_hash = hash1, id = id1}, VOBJ{obj_hash = hash2, id = id2}) => VBOOL (id1 = id2)
        | (VMETHOD {close = close1, this = this1}, VMETHOD{close = close2, this = this2}) => VBOOL (((#id close1) = (#id close2)) andalso ((#id this1) = (#id this2)))
        | (x, y) => VBOOL (false))

    | BOP_NE => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 <> num2)
        | (VSTR str1, VSTR str2) => VBOOL (str1 <> str2)
        | (VBOOL bool1, VBOOL bool2) => VBOOL (bool1 <> bool2)
        | (x, y) => VBOOL (true))

    | BOP_LT => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 < num2)
        | (x, y) => raise RelationalException (opr, findType x, findType y))
    
    | BOP_GT => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 > num2)
        | (x, y) => raise RelationalException (opr, findType x, findType y))

    | BOP_LE => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 <= num2)
        | (x, y) => raise RelationalException (opr, findType x, findType y))

    | BOP_GE => 
      (case (evalExp(lft, curState, curClassTable), evalExp(rht, curState, curClassTable)) of
        (VNUM num1, VNUM num2) => VBOOL (num1 >= num2)
        | (x, y) => raise RelationalException (opr, findType x, findType y))

    | BOP_AND =>
      (case (evalExp(lft, curState, curClassTable)) of
        (VBOOL bool1) => if bool1 then 
          (case (evalExp(rht, curState, curClassTable)) of
          VBOOL bool2 => VBOOL bool2
          | (y) => raise BooleanSecondException(opr, (findType y)))
          else VBOOL false
        | (x) => raise BooleanFirstException(opr, (findType x)))

    | BOP_OR => 
      (case (evalExp(lft, curState, curClassTable)) of
        (VBOOL bool1) => if bool1 then VBOOL true else
          (case (evalExp(rht, curState, curClassTable)) of
          VBOOL bool2 => VBOOL bool2
          | (y) => raise BooleanSecondException(opr, (findType y)))
        | (x) => raise BooleanFirstException(opr, (findType x)))
  end

and evalUnary (uexp : {opr: unaryOperator, opnd: expression}, curState: state, curClassTable : classTable) : value =
  let val {opr, opnd} = uexp in
    case opr of
    UOP_NOT => 
      (case (evalExp (opnd, curState, curClassTable)) of
        VBOOL x => VBOOL (not x)
        | x => raise UnaryNotException (findType x))

    | UOP_MINUS => 
      (case (evalExp (opnd, curState, curClassTable)) of
        VNUM x => VNUM (~x)
        | x => raise UnaryMinusException (findType x))
  end

and evalConditional (cond: {guard: expression, thenExp: expression, elseExp: expression}, curState : state, curClassTable : classTable) : value = 
  let val {guard, thenExp, elseExp} = cond in
    case (evalExp (guard, curState, curClassTable)) of
    VBOOL x => if x then (evalExp (thenExp, curState, curClassTable)) else (evalExp (elseExp, curState, curClassTable))
    | x => raise ConditionalException (findType x)
  end

and evalExp (exp : expression, curState : state, curClassTable : classTable) : value =
  case exp of
    EXP_ID id =>
      (case curState of 
      [] => raise UndeclaredVariableException id
      | x::xs => (case (find x id) of
        NONE => evalExp (EXP_ID id, xs, curClassTable)
        | SOME x => x))
    | EXP_THIS => 
      (case curState of 
      [] => raise UndeclaredVariableException "this"
      | x::xs => (case (find x "this") of
        NONE => evalExp (EXP_THIS, xs, curClassTable)
        | SOME x => x))

    | EXP_NUM num => VNUM num
    | EXP_STRING str => VSTR str
    | EXP_BOOL tf => VBOOL tf
    | EXP_NONE => VN

    | EXP_BINARY bexp => evalBinary (bexp, curState, curClassTable)
    | EXP_UNARY uexp => evalUnary (uexp, curState, curClassTable)
    | EXP_COND cond => evalConditional (cond, curState, curClassTable)

    | EXP_ASSIGN {lhs = EXP_ID x, rhs} => assignVar (x, evalExp(rhs, curState, curClassTable), curState)
    | EXP_ASSIGN {lhs = EXP_DOT {obj, field}, rhs} => 
      (case (evalExp (obj, curState, curClassTable)) of 
      VOBJ {obj_hash, id} => 
        (case find obj_hash field of
        NONE => raise FieldNotFoundException field
        | SOME fieldVal => 
          let val newFieldVal = evalExp(rhs, curState, curClassTable) in
            (insert obj_hash (field, newFieldVal); newFieldVal)
          end)
      | x => raise FieldSetNonObjectException (field, findType x))
    | EXP_ASSIGN {lhs, rhs} => raise AssignmentTargetException 

    | EXP_CALL {func, args} => 
      (case (evalExp (func, curState, curClassTable)) of 
      VCLOS {func, environment, id} => 
        let 
          val {params, decls, body} = func
          val (newScope) = bindParameters (params, (List.map (fn x => evalExp (x, curState, curClassTable)) args)) in
            (evalStatement (ST_BLOCK {stmts = body}, initializeFunctionVars (decls, newScope::environment), curClassTable); 
            (case find newScope "return" of
            SOME retVal => retVal
            | NONE => VN)) 
        end
      | VMETHOD {close, this} => 
        let 
          val {params, decls, body} = (#func close)
          val withParameters = bindParameters (params, (List.map (fn x => evalExp (x, curState, curClassTable)) args))
          val withFunctionVars =  initializeFunctionVars (decls, withParameters::(#environment close))
          val withThis = insertThis (this, withFunctionVars) in
            (
              evalStatement (ST_BLOCK {stmts = body}, withThis, curClassTable); 
              (case find (hd withThis) "return" of
              SOME retVal => retVal
              | NONE => VN)
            )
        end
      | x => raise NonFunctionException (findType x))
    | EXP_ANON f => VCLOS {func = f, environment = curState, id = ref ()}

    | EXP_NEW {class} => 
      VOBJ {
        obj_hash =
          copy ((case (find curClassTable class) of
          NONE => raise NewException class
          | SOME x => x)), 
        id = ref ()
        }
    | EXP_DOT {obj, field} => 
      (case (evalExp (obj, curState, curClassTable)) of 
      VOBJ gottenObject => 
        let val {obj_hash, id} = gottenObject in
        (case find obj_hash field of
        NONE => raise FieldNotFoundException field
        | SOME fieldVal => 
          (case fieldVal of
          VCLOS x => VMETHOD {close = x, this = gottenObject}
          | y => y))
        end
      | x => raise FieldGetNonObjectException (field, findType x))

and evalBlock (block : {stmts: statement list}, curState : state, curClassTable : classTable) : state =
  let val {stmts} = block in 
    case stmts of
    [] => curState
    | x::xs => 
      let val (newState) = evalStatement(x, curState, curClassTable)
      in
        evalBlock ({stmts = xs}, newState, curClassTable)
      end
  end

and evalIf (ifStmt : {guard: expression, th: statement, el: statement option}, curState : state, curClassTable : classTable) : state =
  let val {guard, th, el} = ifStmt in
    case (evalExp (guard, curState, curClassTable)) of
    VBOOL x => if x then evalStatement (th, curState, curClassTable) else 
      (case el of
      NONE => curState
      | SOME x => evalStatement (x, curState, curClassTable))

    | x => raise IfGuardException (findType x)
  end


and evalPrint (print : {exp: expression}, curState : state, curClassTable : classTable) : state =
  let val {exp} = print in
    case (evalExp (exp, curState, curClassTable)) of
    VNUM x => 
      (if x >= 0 then
       TextIO.output(TextIO.stdOut, Int.toString x) 
       else TextIO.output(TextIO.stdOut, ("-" ^ (Int.toString (abs x))));
        curState)

    | VBOOL x => (TextIO.output(TextIO.stdOut, Bool.toString x); curState)
    | VSTR x => (TextIO.output(TextIO.stdOut, x); curState)
    | VCLOS x => (TextIO.output(TextIO.stdOut, "function"); curState)
    | VOBJ x => (TextIO.output(TextIO.stdOut, "object"); curState)
    | VMETHOD x => (TextIO.output(TextIO.stdOut, "method"); curState)
    | VN => (TextIO.output(TextIO.stdOut, "none"); curState)
  end

and evalWhile (whileStmt : {guard: expression, body: statement}, curState : state, curClassTable : classTable) : state =
  case find (hd curState) "return" of
    SOME y => curState
    | NONE =>
    let val {guard, body} = whileStmt in
      (case (evalExp (guard, curState, curClassTable)) of
      VBOOL x => if x then evalWhile (whileStmt, evalStatement(body, curState, curClassTable), curClassTable) else curState
      | x => raise WhileGuardException (findType x))
    end

and evalStatement (stmt : statement, curState : state, curClassTable : classTable) : state = 
  case find (hd curState) "return" of
    SOME y => curState
    | NONE =>
    (case stmt of
      ST_EXP x => (evalExp ((#exp x), curState, curClassTable); curState)
      | ST_BLOCK x => evalBlock (x, curState, curClassTable)
      | ST_IF x => evalIf (x, curState, curClassTable)
      | ST_PRINT x => evalPrint (x, curState, curClassTable)
      | ST_WHILE x => evalWhile (x, curState, curClassTable)
      | ST_RETURN x => 
        if length(curState) > 1 then 
          (case (#exp x) of
          SOME x => (insert (hd curState) ("return", evalExp(x, curState, curClassTable)); curState)
          | NONE => (insert (hd curState) ("return", VN); curState))
        else raise ReturnOutsideFunctionException)
;

fun evaluate (prog: program) : unit =
  case prog of
    PROGRAM {classes, decls, funcs, stmts} => 
      let val topLevelEnvironment = initializeFunctions (funcs, initializeGlobalVars decls) in
        (evalBlock ({stmts = stmts}, topLevelEnvironment, initializeClasses (classes, topLevelEnvironment)); ())
      end
;

