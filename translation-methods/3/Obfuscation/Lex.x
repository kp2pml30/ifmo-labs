{
module Obfuscation.Lex where

import Obfuscation.Tokens
}

-- I do not want to store position => basic instead of monadic

%wrapper "basic"

$alpha = [a-zA-Z]
$digit = [0-9]
$nl = [\n]
$ws = [\ \r\f\v\n\t]

-- no states => no block comments
@singlecomment = "//" $ws [^\n]*

@name = $alpha ($digit | $alpha)*

@number = $digit+
-- no states => no \"
@str = [\"] [^\"\n]* [\"]
@literal = @number | @str

:-

@singlecomment ;
$ws+ ;

@name { \s -> TName s }
"=" { const TSet }
"(" { const TLParen }
")" { const TRParen }
"{" { const TLCParen }
"}" { const TRCParen }
"," { const TComma }
@literal { TLiteral }
";" { const TSColon }
"*" { const TMul }
"/" { const TDiv }
"-" { const TSub }
"+" { const TAdd }

{
}
