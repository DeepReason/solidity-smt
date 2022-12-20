grammar Expr;

expr
:
	exp = expr (
		'.' key = ID
	) # DotExpression
	| array = expr '[' index = expr']' # ArrayAccess
	| quantifier = ('ForAll' | 'Exists')
	    '('
	        '[' decls = ELEMENTARY_SOLIDITY_VAR_DECL (',' decls = ELEMENTARY_SOLIDITY_VAR_DECL)* ']' ','
	        body = expr
	    ')' # Quantifier
	| type = ELEMENTARY_SOLDITY_TYPE '(' exp = expr ')' # Cast
	| function = expr '(' arguments = expr
	(
		',' arguments = expr
	)* ')' # FunctionCall
	| v=expr op=('@before'|'@after'|'@init') # TimeAnnotation
	| operation=(
		'!'
		| '~'
	) v=expr # Unary
	| left = expr '**' right = expr # Exponential
	| left = expr
	(
		operation =
		(
			'*'
			| '/'
			| '%'
		)
	) right = expr # Multiplicative
	| left = expr
	(
		operation =
		(
			'+'
			| '-'
		)
	) right = expr # Additive
	| left = expr
	(
		operation =
		(
			'>>'
			| '<<'
		)
	) right = expr # Shift
	| left = expr operation = INEQ right = expr # CompareIneq
	| left = expr operation = EQ_DISTINCT right = expr # CompareEqDistinct
	| left = expr '&' right = expr # BitwiseAnd
	| left = expr '^' right = expr # BitwiseXor
	| left = expr '|' right = expr # BitwiseOr
	| left = expr '&&' right = expr # LogicalAnd
    | left = expr '||' right = expr # LogicalOr
	| predicate=expr operation='?' trueRes=expr ':' falseRes=expr # Ternary
	| '(' val=expr ')' # Parens
	| value = ID # Identifier
	| value = INT # Int
	| value = DOUBLE # Double
	| value = BOOLEAN # Boolean
;

ELEMENTARY_SOLIDITY_VAR_DECL: ELEMENTARY_SOLDITY_TYPE WS ID;

ELEMENTARY_SOLDITY_TYPE
:
    'address'
    | 'bool'
    | 'bytes'INT
    | 'int'INT?
    | 'uint'INT?
;

BOOLEAN
:
	'TRUE'
	| 'FALSE'
	| 'True'
	| 'False'
	| 'true'
	| 'false'
;

INEQ
:
	'<'
	| '>'
	| '>='
	| '<='
;

EQ_DISTINCT: '==' | '!=';

ID
:
	[a-zA-Z_][0-9a-zA-Z_]*
;

INT
:
		([1-9] (DIGIT*))
		| '0'
;

DOUBLE
:
	INT
	(
		'.' DIGIT+
	)?
;

fragment DIGIT
:
	[0-9]
;

WS
:
	[ \t\r\n]+ -> skip
;

LINE_COMMENT
:
	'//' ~[\r\n]* -> skip
;