{
module Lex (alexScanTokens) where
import Data.Char (isDigit)
import Types
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-z]
$whitechar = [\ \t\r\f\v\n]

tokens :-
	$whitechar+ ;
	$alpha [$alpha $digit \']* { decodeName }
	"(" { const TLPar }
	")" { const TRPar }
	"->" { const TArr }
	"|-" { const TCtx }
	"=" { const TAssign }
	":" { const TColon }
	"." { const TDot }
	"," { const TComma }
	"\" { const TLam }
	("*" $whitechar*)+ { TIndent . length . filter (== '*') }
	"[rule #" $digit+ "]" { TRule . read . filter isDigit }
{
decodeName "let" = TLet
decodeName "in" = TIn
decodeName "forall" = TForall
decodeName x = TVar x
}
