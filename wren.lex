datatype lexresult = DIV | EOF | EOS | ID of string | LPAREN | NUM of int | BOOL of bool | PLUS | MINUS | TIMES | PRINT | RPAREN | LESS | GRTR | LESSEQ | GRTREQ | EQ | NEQ | AND | OR | NOT | PROGRAM | COLON | COMMA | ASSIGN | VAR | BEGIN | WHILE | DO | SKIP | ENDWHILE | ENDIF | ENDBLK | END | IF | THEN | ELSE | READ | WRITE | IS | TYPE of string | GOTO | PROCEDURE | DECLARE | CONST | STOP

val linenum = ref 1
val error = fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof = fn () => EOF
fun inc ( i ) = i := !(i) + 1
%%
%structure WrenLex
alpha = [A-Za-z];
comma = ":";
digit = [0-9];
ws = [\ \t];
%%
\n       => (inc linenum; lex());
{ws}+    => (lex());
"end;" => (ENDBLK);
";"      => (EOS);
"("      => (LPAREN);
")"      => (RPAREN);
","      => (COMMA);
"<>"	 => (NEQ);
"<="	 => (LESSEQ);
">="	 => (GRTREQ);
":="	 => (ASSIGN);
"<"	 => (LESS);
">"	 => (GRTR);
"="      => (EQ);
"+"	 => (PLUS);
"-"	 => (MINUS);
"*"	 => (TIMES);
"/"	 => (DIV);
":"      => (COLON);
"boolean" => (TYPE yytext);
"integer" => (TYPE yytext);
"procedure"  => (PROCEDURE);
"true"   => (BOOL true);
"false"   => (BOOL false);
"var" 	 => (VAR);
"begin"	 => (BEGIN);
"while"	 => (WHILE);
"do" 	 => (DO);
"if" 	 => (IF);
"then" 	 => (THEN);
"else" 	 => (ELSE);
"read" 	 => (READ);
"write"  => (WRITE);
"end while" => (ENDWHILE);
"end if" => (ENDIF);
"end" => (END);
"or"	 => (OR);
"and"	 => (AND);
"not"	 => (NOT);
"is"	 => (IS);
"skip"	 => (SKIP);
"program" => (PROGRAM);
"goto"    => (GOTO);
"declare" => (DECLARE);
"const" => (CONST);
"stop" => (STOP);
{alpha}+{digit}* => (if yytext="print" then PRINT else ID yytext);
{digit}+ => (NUM (foldl (fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (explode yytext)));
.               => (error ("WrenLex: ignoring bad character "^yytext); lex());
