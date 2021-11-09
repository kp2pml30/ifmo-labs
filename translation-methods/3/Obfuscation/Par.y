{
module Obfuscation.Par where

import Control.Monad

import Obfuscation.Tokens
import Obfuscation.Obf
}

%name parse
%tokentype { Token }
%error { parseError }

%token
	type { TName n | n `elem` ["int", "char", "void"] }
	return { TName "return" }
	if { TName "if" }
	else { TName "else" }
	name { TName $$ }
	literal { TLiteral $$ }
	'=' { TSet }
	'(' { TLParen }
	')' { TRParen }
	'{' { TLCParen }
	'}' { TRCParen }
	',' { TComma }
	';' { TSColon }
	'*' { TMul }
	'/' { TDiv }
	'+' { TAdd }
	'-' { TSub }

%left '+' '-'
%left '*' '/'

%%

File
	: Func { [$1] }
	| Func File { $1:$2 }

Func
	: Type name '(' Arguments ')' '{' Body '}' { mkFunc ($1 ++ " " ++ $2) $4 (rndAction $7) }

Type
	: Unwraptype Asteriscs { $1 ++ $2 }

Unwraptype
	: type { let TName x = $1 in x }

Asteriscs
	: { "" }
	| '*' Asteriscs { '*':$2 }

Arguments
	: { [] }
	| SomeArguments { $1 }

SomeArguments
	: Argument { [$1] }
	| Argument ',' SomeArguments { $1:$3 }

Argument
	: Type name { ($1, $2) }

Body
	: { rndAction (return "") }
	| Statement Body { rndAction $ liftM2 (++) $1 $2 }
	| Decl Body { rndAction $ bodyDecl $1 $2 }

Decl
	: Type name '=' Expr ';' { ($1, $2, $4) }

Statement
	: Expr ';' { (++ ";") `fmap` $1 }
	| return ';' { return "return;" }
	| return Expr ';' { (\x -> "return " ++ x ++ ";") `fmap` $2 }
	| if '(' Expr ')' '{' Body '}' Else { mkIf $3 $6 $8 }

Else
	: { return "" :: Md }
	| else '{' Body '}' { (\x -> "else{" ++ x ++ "}") `fmap` $3 }

Expr
	: name { mkName $1 } -- todo
	| literal { return $1 }
	| Expr '+' Expr { bopLift "+" $1 $3 }
	| Expr '-' Expr { bopLift "-" $1 $3 }
	| Expr '*' Expr { bopLift "*" $1 $3 }
	| Expr '/' Expr { bopLift "/" $1 $3 }
	| Expr '(' CallArguments ')' { mkCall $1 $3 }
	| '(' Expr ')' { (\x -> "(" ++ x ++ ")") `fmap` $2 }

CallArguments
	: { return "" :: Md }
	| SomeCallArguments { $1 }

SomeCallArguments
	: Expr { $1 }
	| Expr ',' SomeCallArguments { bopLift "," $1 $3 }

{
parseError :: [Token] -> a
parseError x = error ("Parse error " ++ (show $ take 10 x))
}
