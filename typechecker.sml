use "exceptions.sml";

type mapping =
  (string * type') list
;

fun parameterTypes (parameters: type' list) : string =
  case parameters of
    [] => ""
    | [x] => typeOf x
    | x::xs => (typeOf x) ^ "*" ^ (parameterTypes xs)

and typeOf (t : type') : string =
  case t of
  TY_BOOL => "bool"
  | TY_INT => "int"
  | TY_STRING => "string"
  | TY_FUNC {in_types, ret_type} => "(" ^ (parameterTypes in_types) ^ " -> " ^ (typeOf ret_type) ^ ")"
  | TY_NONE => "none"
;

fun seconds (t : ('a * 'b) list) : 'b list =
  if null t
  then []
  else #2 (hd t)::seconds(tl t)
;

fun checkVarDeclarations (decls: decl list) : mapping =
  case decls of
  [] => []
  | x::xs => 
    let val curMapping = checkVarDeclarations (xs) in
      (case List.find (fn (y, _) => (y) = (#1 x)) curMapping of
      SOME pair => raise VariableRedeclarationException (#1 x)
      | NONE => (x)::curMapping)
    end

and checkFunDeclarations (func_decls: (string * function) list, curMapping) : mapping =
  case func_decls of
  [] => curMapping
  | (id, func)::xs => 
    (case List.find (fn (y, _) => (y) = (id)) curMapping of
    SOME pair => raise VariableRedeclarationException (id)
    | NONE => 
      let val (newMapping) = checkFunDeclarations (xs, (id, TY_FUNC {in_types = seconds (#params func), ret_type = (#ret_type func)})::curMapping) in
        ((checkExpression (EXP_ANON func, newMapping)); newMapping)
      end)

and checkArgs (args: expression list, param_types: type' list, curMapping: mapping) : bool =
  case (args, param_types) of
  ([], []) => true
  | ([], _) => raise CallTooFewArgumentsException
  | (_, []) => raise CallTooManyArgumentsException
  | (x::xs, y::ys) =>
      let val argType = checkExpression (x, curMapping) in
        if argType = y then checkArgs(xs, ys, curMapping) 
        else raise ArgumentException (typeOf argType, typeOf y)
      end

and checkReturnPath (stmt_list : statement list) : bool =
  case stmt_list of
  [ST_RETURN x] => true
  | x::xs => checkReturnPath (xs)
  | [] => false
  
and checkStatement (stmt: statement, curMapping: mapping) : mapping =
    case stmt of
      ST_EXP {exp} => (checkExpression (exp, curMapping); curMapping)
      | ST_BLOCK x => checkBlock (x, curMapping)
      | ST_IF {guard, th, el} => 
        (case checkExpression (guard, curMapping) of
        TY_BOOL => (checkStatement (th, curMapping); 
        (case el of 
        SOME elStmt => checkStatement (elStmt, curMapping)
        | NONE => curMapping); curMapping)
        | x => raise IfGuardException (typeOf x))
      | ST_PRINT {exp} => (checkExpression (exp, curMapping); curMapping)
      | ST_WHILE {guard, body} => 
        (case checkExpression (guard, curMapping) of
        TY_BOOL => checkStatement (body, curMapping)
        | x => raise WhileGuardException (typeOf x))
      | ST_RETURN {exp} => 
        (case exp of 
        SOME ret_exp =>
          (case List.find (fn (y, _) => y = "return") curMapping of
          SOME ret_type =>
            let val (st_type) = checkExpression(ret_exp, curMapping) in
              if st_type = (#2 ret_type)
              then curMapping
              else raise ReturnTypeException (typeOf st_type, typeOf (#2 ret_type))
            end
          | NONE => raise ReturnOutsideFunctionException)
        | NONE => curMapping)

and checkExpression (exp: expression, curMapping: mapping) : type' =
  case exp of 
  EXP_ID id => 
     (case (List.find (fn (y, _) => y = id) curMapping) of
        NONE => raise UndeclaredVariableException (id)
        | SOME x => (#2 x))
  | EXP_NUM num => TY_INT
  | EXP_STRING str => TY_STRING
  | EXP_BOOL bool => TY_BOOL
  | EXP_NONE => TY_NONE

  | EXP_BINARY bexp => checkBinary (bexp, curMapping)
  | EXP_UNARY uexp => checkUnary (uexp, curMapping)
  | EXP_COND cond => checkConditional (cond, curMapping)
  
  | EXP_ASSIGN {lhs = EXP_ID x, rhs} =>
    (case (checkExpression (EXP_ID x, curMapping), checkExpression (rhs, curMapping)) of
    (t1, t2) => if t1 = t2 then t1 else raise AssignmentTypeException (typeOf t1, typeOf t2))
  | EXP_ASSIGN {lhs, rhs} => raise AssignmentTargetException 

  | EXP_CALL {func, args} => 
      (case (checkExpression (func, curMapping)) of 
      TY_FUNC {in_types, ret_type} => (checkArgs(args, in_types, curMapping); ret_type)
      | x => raise NonFunctionException (typeOf x))

  | EXP_ANON {params, decls, body, ret_type: type'} => 
    (case checkVarDeclarations (params @ decls) of
    x => 
      let val (newMapping) = (decls @ params @ ("return", ret_type)::curMapping) in
        if (ret_type = TY_NONE) orelse checkReturnPath (body) then
        (checkBlock ({stmts = body}, newMapping); TY_FUNC {in_types = seconds (params), ret_type = ret_type})
        else raise ReturnPathException
      end)

and checkBinary (bexp : {opr: binaryOperator, lft: expression, rht: expression}, curMapping : mapping) : type' =
  let val {opr, lft, rht} = bexp in
    case opr of 
    BOP_PLUS => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_INT
        | (TY_STRING, TY_STRING) => TY_STRING
        | (x, y) => raise AddException (typeOf x, typeOf y))

    | BOP_MINUS =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_INT
        | (x, y) => raise ArithmeticException (opr, typeOf x, typeOf y))

    | BOP_TIMES =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_INT
        | (x, y) => raise ArithmeticException (opr, typeOf x, typeOf y))

    | BOP_DIVIDE => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_INT
        | (x, y) => raise ArithmeticException (opr, typeOf x, typeOf y))

    | BOP_MOD =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_INT
        | (x, y) => raise ArithmeticException (opr, typeOf x, typeOf y))

    | BOP_EQ => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (TY_STRING, TY_STRING) => TY_BOOL
        | (TY_BOOL, TY_BOOL) => TY_BOOL
        | (TY_NONE, TY_NONE) => TY_BOOL
        | (TY_FUNC a, TY_FUNC b) => TY_BOOL
        | (x, y) => raise EqualityTypeException (opr, typeOf x, typeOf y))

    | BOP_NE => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (TY_STRING, TY_STRING) => TY_BOOL
        | (TY_BOOL, TY_BOOL) => TY_BOOL
        | (TY_NONE, TY_NONE) => TY_BOOL
        | (TY_FUNC a, TY_FUNC b) => TY_BOOL
        | (x, y) => raise EqualityTypeException (opr, typeOf x, typeOf y))

    | BOP_LT => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (x, y) => raise RelationalException (opr, typeOf x, typeOf y))

    | BOP_GT =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (x, y) => raise RelationalException (opr, typeOf x, typeOf y))

    | BOP_LE =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (x, y) => raise RelationalException (opr, typeOf x, typeOf y))

    | BOP_GE => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_INT, TY_INT) => TY_BOOL
        | (x, y) => raise RelationalException (opr, typeOf x, typeOf y))

    | BOP_AND => 
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_BOOL, TY_BOOL) => TY_BOOL
        | (x, y) => raise BooleanException (opr, typeOf x, typeOf y))

    | BOP_OR =>
        (case (checkExpression(lft, curMapping), checkExpression(rht, curMapping)) of
        (TY_BOOL, TY_BOOL) => TY_BOOL
        | (x, y) => raise BooleanException (opr, typeOf x, typeOf y))
   end

and checkUnary (uexp : {opr: unaryOperator, opnd: expression}, curMapping: mapping) : type' =
  let val {opr, opnd} = uexp in
    case opr of
    UOP_NOT => 
      (case (checkExpression (opnd, curMapping)) of
        TY_BOOL => TY_BOOL
        | x => raise UnaryNotException (typeOf x))

    | UOP_MINUS => 
      (case (checkExpression (opnd, curMapping)) of
        TY_INT => TY_INT
        | x => raise UnaryMinusException (typeOf x))
   end

and checkConditional (cond: {guard: expression, thenExp: expression, elseExp: expression}, curMapping : mapping) : type' = 
  let val {guard, thenExp, elseExp} = cond in
    case checkExpression (guard, curMapping) of
    TY_BOOL => 
      (case (checkExpression (thenExp, curMapping), checkExpression (elseExp, curMapping)) of
      (t1, t2) => if t1 = t2 then t1 else raise ConditionalTypeException (typeOf t1, typeOf t2))
    | x => raise ConditionalException (typeOf x)
  end

and checkBlock (block : {stmts: statement list}, curMapping : mapping) : mapping =
  let val {stmts} = block in 
    case stmts of
    [] => curMapping
    | x::xs => 
      let val (newMapping) = checkStatement(x, curMapping)
      in
        checkBlock ({stmts = xs}, newMapping)
      end
  end
;

fun typecheck (prog: program) : unit =
  case prog of
    PROGRAM {decls, func_decls, stmts} => (checkBlock ({stmts = stmts}, checkFunDeclarations (func_decls, checkVarDeclarations decls)); ())
;