{
module Par (parse) where
import Types
}

%name parse
%tokentype { Token }
%error { parseError }

%token
	indent { TIndent $$ }
	let { TLet }
	in { TIn }
	forall { TForall }
	rule { TRule $$ }
	var { TVar $$ }
	'(' { TLPar }
	':' { TColon }
	'.' { TDot }
	',' { TComma }
	')' { TRPar }
	'->' { TArr }
	'=' { TAssign }
	'|-' { TCtx }
	lam { TLam }

%%

File
	: { [] }
	| Row File { $1 : $2 }

Row
	: indent Context '|-' TypedExpr rule { Row $1 $2 $4 $5 }

Context
	: { [] }
	| ContextSome { $1 }

ContextSome
	: ContextEl { [$1] }
	| ContextEl ',' ContextSome { $1 : $3 }

ContextEl
	: var ':' Type { ($1, $3) }

TypedExpr
	: Expr ':' Type { TypedExpr $1 $3 }

Type
	: '(' Type ')' { $2 }
	| Monotype { MType $1 }
	| forall var '.' Type { Forall $2 $4 }

Monotype
	: var MonotypeAppendix { $2 (Type $1) }
	| '(' Monotype ')' MonotypeAppendix { $4 $2 }

MonotypeAppendix
	: { id }
	| '->' Monotype { \x -> Arr x $2 }

Expr
	: Lam { $1 }
	| let var '=' Expr in Expr { Let $2 $4 $6 }
	| Application MbLam { $2 $1 }

MbLam
	: { id }
	| Lam { \x -> Appl x $1 }

Lam
	: lam var '.' Expr { Lam $2 $4 }

Application
	: Atom { $1 }
	| Application Atom { Appl $1 $2 }

Atom
	: '(' Expr ')' { $2 }
	| var { Var $1 }

{
parseError :: [Token] -> a
parseError x = error ("Parse error " ++ (show x))
}
