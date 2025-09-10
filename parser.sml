use "tokenizer.sml";
use "ast.sml";
use "exceptions_parser.sml";

exception InvalidOperatorException of string * token;

fun error message =
   (TextIO.output (TextIO.stdErr, message ^ "\n");
    OS.Process.exit OS.Process.failure)
;

fun match_token expected (token::tokens) =
   if token = expected
   then tokens
   else raise InvalidTokenException
      {expected=token_string expected, found=token_string token}
  | match_token expected [] =
      raise ExhaustedTokensException (token_string expected)
;

fun match_id (TK_ID id::tokens) = (id, tokens)
  | match_id (token::_) = raise InvalidIdentifierException (token_string token)
  | match_id [] = raise ExhaustedTokensException "identifier"
;

fun find_pair s xs = List.find (fn (st, _) => st = s) xs;
fun in_ops ops token = isSome (find_pair token ops);

val eqOps = [(TK_EQ, BOP_EQ), (TK_NE, BOP_NE)];
val relOps = [(TK_LT, BOP_LT), (TK_GT, BOP_GT), (TK_LE, BOP_LE),
   (TK_GE, BOP_GE)];
val addOps = [(TK_PLUS, BOP_PLUS), (TK_MINUS, BOP_MINUS)];
val multOps = [(TK_TIMES, BOP_TIMES), (TK_DIVIDE, BOP_DIVIDE),
   (TK_MOD, BOP_MOD)];
val unaryOps = [(TK_NOT, UOP_NOT), (TK_MINUS, UOP_MINUS)];
val andOps = [(TK_AND, BOP_AND)];
val orOps = [(TK_OR, BOP_OR)];

fun opErrorMsgList [] strs= []
  | opErrorMsgList ((x, _)::[]) strs = (token_string x) :: strs
  | opErrorMsgList ((x, _)::(y, _)::[]) strs =
       (token_string y)::" or "::(token_string x) :: strs
  | opErrorMsgList ((x, _)::(y, _)::(z, _)::[]) strs =
      (token_string z)::", or "::(token_string y)::", "::(token_string x)::strs
  | opErrorMsgList ((x, _)::xs) strs =
      opErrorMsgList xs (", "::(token_string x)::strs)
;
fun opErrorMsg ops = foldl (op ^) "" (opErrorMsgList ops []);

val is_eq_op    = in_ops eqOps;
val is_rel_op   = in_ops relOps;
val is_add_op   = in_ops addOps;
val is_mult_op  = in_ops multOps;
val is_unary_op = in_ops unaryOps;
val is_and_op   = in_ops andOps;
val is_or_op    = in_ops orOps;

fun is_var TK_VAR = true
  | is_var _ = false
;

fun is_expression token =
   case token of
      (TK_LPAREN | (TK_ID _) | (TK_NUM _) | (TK_STRING _) | TK_TRUE
         | TK_FALSE | TK_NONE | TK_NOT | TK_MINUS) => true
    | _ => false
;

fun isValidLHS (EXP_ID _) = true
  | isValidLHS _ = false
;

fun is_statement token =
   case token of
      (TK_LBRACE | TK_IF | TK_PRINT | TK_WHILE) => true
    | _ => is_expression token
;

fun parse_repetition tokens pred parse_single =
   let
      fun repeat tokens xs =
         if not (null tokens) andalso pred (hd tokens)
         then
            let
               val (x, tokens1) = parse_single tokens;
            in
               repeat tokens1 (x::xs)
            end
         else
            (rev xs, tokens)
      ;
   in
      repeat tokens []
   end
;

(* expression parsing functions *)
fun parse_op ops token =
   case find_pair token ops of
      SOME (tk1, opr) => opr
   |  NONE => raise InvalidOperatorException (opErrorMsg ops, token)
;

val parse_eq_op      = parse_op eqOps;
val parse_rel_op     = parse_op relOps;
val parse_add_op     = parse_op addOps;
val parse_mult_op    = parse_op multOps;
val parse_unary_op   = parse_op unaryOps;
val parse_and_op     = parse_op andOps;
val parse_or_op      = parse_op orOps;

fun parse_binary_exp_left tokens parse_opnd is_opr parse_opr =
   let
      fun repeat tokens lft =
         if not (null tokens) andalso is_opr (hd tokens)
         then
            let
               val opr = parse_opr (hd tokens);
               val (rht, tokens2) = parse_opnd (tl tokens);
            in
               repeat tokens2 (EXP_BINARY {opr=opr, lft=lft, rht=rht})
            end
         else (lft, tokens)
      ;
      val (lft, tokens1) = parse_opnd tokens;
   in
      repeat tokens1 lft
   end
;

fun parse_expression tokens =
   (case parse_conditional_expression tokens of
      (lhs, TK_ASSIGN::tokens1) =>
         if isValidLHS lhs
         then
            let
               val (rhs, tokens2) = parse_expression tokens1;
            in
               (EXP_ASSIGN {lhs=lhs, rhs=rhs}, tokens2)
            end
         else raise InvalidAssignException
   |  ret => ret
   )
and parse_conditional_expression tokens =
   (case parse_logical_or_expression tokens of
      (guard, TK_QUESTION::tokens1) =>
         let
            val (thenExp, tokens2) = parse_expression tokens1;
            val tokens3 = match_token TK_COLON tokens2;
            val (elseExp, tokens4) = parse_expression tokens3;
         in
            (EXP_COND {guard=guard, thenExp=thenExp, elseExp=elseExp}, tokens4)
         end
   |  ret => ret
   )
and parse_logical_or_expression tokens =
   parse_binary_exp_left tokens parse_logical_and_expression
      is_or_op parse_or_op
and parse_logical_and_expression tokens =
   parse_binary_exp_left tokens parse_equality_expression is_and_op parse_and_op
and parse_equality_expression tokens =
   parse_binary_exp_left tokens parse_relational_expression is_eq_op parse_eq_op
and parse_relational_expression tokens =
   parse_binary_exp_left tokens parse_additive_expression is_rel_op parse_rel_op

and parse_additive_expression tokens =
   parse_binary_exp_left tokens parse_multiplicative_expression
      is_add_op parse_add_op

and parse_multiplicative_expression tokens =
   parse_binary_exp_left tokens parse_unary_expression is_mult_op parse_mult_op

and parse_unary_expression tokens =
   if not (null tokens) andalso is_unary_op (hd tokens)
   then
      let
         val opr = parse_unary_op (hd tokens);
         val (opnd, tokens1) = parse_call_member_expression (tl tokens);
      in
         (EXP_UNARY {opr=opr, opnd=opnd}, tokens1)
      end
   else parse_call_member_expression tokens

and parse_call_member_expression tokens =
   parse_primary_expression tokens

and parse_primary_expression (TK_LPAREN::tokens) =
   let
      val (exp, tokens1) = parse_expression tokens;
      val tokens2 = match_token TK_RPAREN tokens1;
   in
      (exp, tokens2)
   end
  | parse_primary_expression (TK_ID id::tokens) = (EXP_ID id, tokens)
  | parse_primary_expression (TK_NUM n::tokens) = (EXP_NUM n, tokens)
  | parse_primary_expression (TK_TRUE::tokens) = (EXP_BOOL true, tokens)
  | parse_primary_expression (TK_FALSE::tokens) = (EXP_BOOL false, tokens)
  | parse_primary_expression (TK_NONE::tokens) = (EXP_NONE, tokens)
  | parse_primary_expression (TK_STRING s::tokens) = (EXP_STRING s, tokens)
  | parse_primary_expression (token::_) =
      raise InvalidExpressionException (token_string token)
  | parse_primary_expression [] = raise ExhaustedTokensException "expression"
;

(* statement parsing functions *)
fun parse_expression_statement tokens =
   let
      val (exp, tokens1) = parse_expression tokens;
      val tokens2 = match_token TK_SEMI tokens1;
   in
      (ST_EXP {exp=exp}, tokens2)
   end
;

fun parse_statement (tokens as token::_) =
   (case token of
      TK_LBRACE => parse_block_statement tokens
    | TK_IF => parse_if_statement tokens
    | TK_PRINT => parse_print_statement tokens
    | TK_WHILE => parse_while_statement tokens
    | _ => if is_expression token
           then parse_expression_statement tokens
           else raise InvalidStatementException (token_string token)
   )
  | parse_statement [] = raise ExhaustedTokensException "statement"

and parse_block_statement tokens =
   let
      val tokens1 = match_token TK_LBRACE tokens;
      val (stmts, tokens2) = parse_statements tokens1;
      val tokens3 = match_token TK_RBRACE tokens2;
   in
      (ST_BLOCK {stmts=stmts}, tokens3)
   end
and parse_if_statement tokens =
   let
      val tokens1 = match_token TK_IF tokens;
      val tokens2 = match_token TK_LPAREN tokens1;
      val (guard, tokens3) = parse_expression tokens2;
      val tokens4 = match_token TK_RPAREN tokens3;
      val (th, tokens5) = parse_block_statement tokens4;
      val (el, tokens6) = parse_else tokens5;
   in
      (ST_IF {guard=guard, th=th, el=el}, tokens6)
   end

and parse_else (TK_ELSE::tokens) =
   let
      val (el, tokens1) = parse_block_statement tokens;
   in
      (SOME el, tokens1)
   end
  | parse_else tokens =
      (NONE, tokens)

and parse_print_statement tokens =
   let
      val tokens1 = match_token TK_PRINT tokens;
      val (exp, tokens2) = parse_expression tokens1;
      val tokens3 = match_token TK_SEMI tokens2;
   in
      (ST_PRINT {exp=exp}, tokens3)
   end

and parse_while_statement tokens =
   let
      val tokens1 = match_token TK_WHILE tokens;
      val tokens2 = match_token TK_LPAREN tokens1;
      val (guard, tokens3) = parse_expression tokens2;
      val tokens4 = match_token TK_RPAREN tokens3;
      val (body, tokens5) = parse_block_statement tokens4;
   in
      (ST_WHILE {guard=guard, body=body}, tokens5)
   end

and parse_statements tokens =
   parse_repetition tokens is_statement parse_statement
;

fun parse_var_declaration (TK_VAR::tokens) =
   let
      val (id, tokens1) = match_id tokens;
      val tokens2 = match_token TK_SEMI tokens1;
   in
      (id, tokens2)
   end
  | parse_var_declaration (token::_) =
      raise InvalidTokenException
         {expected=token_string TK_VAR, found=token_string token}
  | parse_var_declaration [] =
      raise ExhaustedTokensException "variable declaration"
;
   

fun parse_var_declarations tokens =
   parse_repetition tokens is_var parse_var_declaration
;

fun parse tokens =
   let
      val (decls, tokens1) = parse_var_declarations tokens;
      val (stmts, tokens2) = parse_statements tokens1;
   in
      if null tokens2
      then PROGRAM {decls=decls, stmts=stmts}
      else raise InvalidEndOfProgramException (token_string (hd tokens2))
   end
;

fun parse_file file =
   parse (tokenize (TextIO.inputAll (TextIO.openIn file)))
      handle
           InvalidSymbolException s => error ("invalid symbol: " ^ s)
         | UnterminatedStringException => error "unterminated string"
         | InvalidEscapeSequenceException c =>
            error ("invalid escape sequence: \\" ^ (str c))
         | InvalidEscapeMissingException =>
            error "unterminated escape sequence"
         | IllegalCharacterException c =>
            error ("illegal chracter: " ^ (str c))
         | InvalidNumberException s =>
            error ("invalid number token: " ^ s)
         | InvalidStringException =>
            error ("invalid start of string token")
         | InvalidWhitespaceInStringException =>
            error ("invalid whitespace in string")
         | InvalidAssignException => error ("unexpected '='")
         | InvalidIdentifierException token =>
            error ("expected 'identifier', found '" ^ token ^ "'")
         | InvalidTokenException {expected, found} =>
            error ("expected '" ^ expected ^ "', found '" ^ found ^ "'")
         | InvalidExpressionException token =>
            error ("expected 'value', found '" ^ token ^ "'")
         | InvalidStatementException token =>
            error ("invalid start of statement '" ^ token ^ "'")
         | ExhaustedTokensException msg =>
            error ("expected '" ^ msg ^ "', no token found")
         | InvalidEndOfProgramException token =>
            error ("token '" ^ token ^ "' after logical end of program")
;
