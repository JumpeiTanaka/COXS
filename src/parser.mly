/*
@original author: Vandang Tran
@updated by: Jumpei Tanaka
 */

%{ (* OCaml preamble *)

  open Expr ;;
  open Utils ;;
  (* let parse_error (s : string) = spec_parse_error s 1;; *)
  (* end preamble *)
 %}


/* tokens declaration */

%token <int> INT               /* token with int value */
%token <float> FLOAT           /* token with float value */
%token <string> STRING         /* token with string value */
%token <string> NAME           /* token with string value */
%token <string> VARNAME        /* token with string value */

%token QMARK SMARK VMARK TMARK DOT IMPLIEDBY PK
%token RMARK RINMARK
%token TYPING SINT SREAL SSTRING SBOOL
%token AND NOT OR TT FF BOT TOP
%token NULL
%token EQ
%token NE LE GE LT GT
%token PLUS MINUS TIMES DIVIDE CONCAT
%token LPAREN RPAREN LBRACKET RBRACKET SEP
%token EOP
%token EOF
%token ANONVAR /* anonymous variable */
%token ANON   /* fake token to stop the grammar in the fact rule */

%token SKOLEM /* to be deleted (Jumpei Tanaka) */
%token SHARP

/* associativity and precedence when needed */
%nonassoc IMPLIEDBY


%start main               /*  entry point    */
%type <Expr.expr> main
%%

/* Grammar */
  main:	EOF	          { Prog [] }
  | program  EOF      { Prog (List.rev $1)  }
  | error             { spec_parse_error "invalid syntax for a main program" 1; }
  ;

  program:
  exprlist						{ $1 }
  | error             { spec_parse_error "invalid syntax for a program" 1; }
  ;

  exprlist:
  | expr							{ $1 :: [] }
  | exprlist expr 		{ $2 :: $1 }
  | error             { spec_parse_error "invalid syntax for a list of rules" 1; }
  ;

  expr:
  | primary_key              { $1 }
  | integrity_constraint     { $1 }
  | rule	                   { $1 }
  | query	                   { $1 }
  | source_schema	           { $1 }
  | target_schema            { $1 }
  | error                    { spec_parse_error "invalid syntax for a rule or a declaration of query/source/view/constraint" 1; }
  ;

/*
  fact:
  literal                    { $1 }
  | error                    { spec_parse_error "invalid syntax for a fact" 1; }
  ;
*/

  primary_key:
  | PK LPAREN NAME SEP LBRACKET attrlist RBRACKET RPAREN	DOT	{ Pk ($3, $6) }
  | PK LPAREN NAME SEP LBRACKET attrlist RBRACKET RPAREN EOF	{ spec_parse_error "miss a dot for a primary key" 3; }
  | error             { spec_parse_error "invalid syntax for a primary key" 1; }
  ;

  attrlist: /* empty */				{ [] }
  | STRING				    				{ String.uppercase_ascii (String.sub $1 1 (String.length $1 - 2)) :: [] }
  | STRING SEP attrlist 			{ String.uppercase_ascii (String.sub $1 1 (String.length $1 - 2)) :: $3 } /* \!/ rec. on the right */
  | error             { spec_parse_error "invalid syntax for a list of attributes" 1; }
  ;

  integrity_constraint:
  | BOT IMPLIEDBY body DOT				              	{ Constraint ( get_empty_pred, $3) }
  | BOT LPAREN RPAREN IMPLIEDBY body DOT					{ Constraint ( Pred ("⊥", []), $5) }
  | BOT IMPLIEDBY body EOF					              { spec_parse_error "miss a dot for a constraint" 3; }
  | error                                         { spec_parse_error "invalid syntax for a constraint" 1; }
  ;

  rule:
  head IMPLIEDBY body DOT			   	{ Rule ($1,$3) }
  | head IMPLIEDBY body EOF       { spec_parse_error "miss a dot for a rule" 4; }
  | error                         { spec_parse_error "invalid syntax for a rule" 1; }
  ;

  head:
  predicate						{ $1 }
  | error             { spec_parse_error "invalid syntax for a head" 1; }
  ;

  body:
  litlist						{ List.rev $1 }
  | error           { spec_parse_error "invalid syntax for a body" 1; }
  ;

  query:
  | QMARK predicate DOT					{ Query $2 }
  | QMARK predicate EOF					{ spec_parse_error "miss a dot for a query" 3; }
  | error                       { spec_parse_error "invalid syntax for a query" 1; }
  ;

  source_schema:
  | SMARK NAME SHARP rel_schema DOT	{ Source_schema ($2, fst $4, snd $4) }
  | SMARK NAME SHARP rel_schema EOF  { spec_parse_error "miss a dot for a source schema" 3; }
  | error                     { spec_parse_error "invalid syntax for a source schema" 1; }
  ;

  target_schema:
  | TMARK NAME SHARP rel_schema DOT	{ Target_schema ($2, fst $4, snd $4) }
  | TMARK NAME SHARP rel_schema EOF  { spec_parse_error "miss a dot for a target schema" 3; }
  | error                     { spec_parse_error "invalid syntax for a target schema" 1; }
  ;

  rel_schema:
  | NAME LPAREN attrtypelist RPAREN		{ ($1, $3) }
  | error                                 { spec_parse_error "invalid syntax for a predicate" 1; }
  ;

  attrtypelist: /* empty */					{ [] }
  | STRING TYPING stype { (String.uppercase_ascii (String.sub $1 1 (String.length $1 - 2)), $3) :: [] }
  | STRING TYPING stype SEP attrtypelist 					{ (String.uppercase_ascii (String.sub $1 1 (String.length $1 - 2)), $3) :: $5 } /* \!/ rec. on the right */
  | error             { spec_parse_error "invalid syntax for a list of pairs of an attribute and its type" 1; }
  ;

  stype:
  | SINT { Sint }
  | SREAL { Sreal }
  | SSTRING { Sstring }
  | SBOOL { Sbool }

  litlist: /* empty */			{ [] }
  | literal						      { $1 :: [] }
  | litlist AND literal			{ $3 :: $1 }
  | litlist SEP literal			{ $3 :: $1 }
  | error             { spec_parse_error "invalid syntax for a conjunction of literals" 1; }
  ;

  literal:
  | predicate							{ Rel $1 }
  | NOT predicate 				{ Not $2 }
  | equation							{ $1 }
  | NOT equation				  { negate_eq $2 }
  | error                 { spec_parse_error "invalid syntax for a literal" 1; }
  ;

  predicate:
  | NAME LPAREN varlist RPAREN	      	{ Pred ($1, $3) }
  | PLUS NAME LPAREN varlist RPAREN		{ Deltainsert ($2, $4) }
  | MINUS NAME LPAREN varlist RPAREN		{ Deltadelete ($2, $4) }
  | error                                 { spec_parse_error "invalid syntax for a predicate" 1; }
  ;

  equation:
  | value_expression EQ value_expression	{ Equal ($1, $3) }
  | value_expression NE value_expression	{ Ineq ("<>", $1, $3) }
  | value_expression LT value_expression	{ Ineq ( "<", $1, $3) }
  | value_expression GT value_expression	{ Ineq ( ">", $1, $3) }
  | value_expression LE value_expression	{ Ineq ("<=", $1, $3) }
  | value_expression GE value_expression	{ Ineq (">=", $1, $3) }
  | error                                 { spec_parse_error "invalid syntax for a comparison" 1; }
  ;

  value_expression:
  | term                          {$1}
  | value_expression PLUS term    {Sum ($1, $3)}
  | value_expression CONCAT term  {Concat ($1, $3)}
  | value_expression MINUS term   {Diff ($1, $3)}
  | error                         { spec_parse_error "invalid syntax for a arithmetic expression" 1; }

  term:
  | factor              {$1}
  | term TIMES factor   {Times ($1, $3)}
  | term DIVIDE factor  {Div ($1, $3)}
  | error               { spec_parse_error "invalid syntax for a term" 1; }

  factor:
  | value_primary   {$1}
  | error           { spec_parse_error "invalid syntax for a factor" 1; }

  value_primary:
  | parenthesized_value_expression       {$1}
  | MINUS parenthesized_value_expression {Neg $2}
  | nonparenthesized_value_primary       {$1}
  | error                                { spec_parse_error "invalid syntax for a primary number" 1; }

  nonparenthesized_value_primary:
  | constant        {Const $1}
  | var_or_agg      {Var $1}
  | error           { spec_parse_error "invalid syntax for a primar number" 1; }

  parenthesized_value_expression:
  | LPAREN value_expression RPAREN   {$2}
  | error                            { spec_parse_error "invalid syntax for a parenthesized expression" 1; }


  var_or_agg:
  | VARNAME     { NamedVar $1 }
  | aggregate   { $1 }
  | error       { spec_parse_error "invalid syntax for a var or a aggreation" 1; }
  ;

  constant:
  | INT               {Int $1}
  | MINUS INT         {Int (- $2)}
  | FLOAT             {Real $1}
  | MINUS FLOAT       {Real (-. $2)}
  | STRING            {String $1}
  | NULL              {Null}
  | FF                {Bool false}
  | TT                {Bool true}
  | error             { spec_parse_error "invalid syntax for a constant" 1; }
  ;

  varlist: /* empty */		{ [] }
  | var				    				{ $1 :: [] }
  | var SEP varlist 			{ $1 :: $3 } /* \!/ rec. on the right */
  | error                 { spec_parse_error "invalid syntax for a list of variables" 1; }
  ;

  var:
  | VARNAME     { NamedVar $1 }
  | ANONVAR     { AnonVar }
  | constant    { ConstVar $1 }
  | aggregate   { $1 }
  | error       { spec_parse_error "invalid syntax for a variables" 1; }
  ;

  aggregate:
  | VARNAME LPAREN VARNAME RPAREN   { AggVar ($1,$3) }
  | error                           { spec_parse_error "invalid syntax for a aggregation" 1; }
  ;
