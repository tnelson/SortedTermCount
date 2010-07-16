
package edu.wpi.termcount;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import java_cup.runtime.Symbol;
import kodkod.ast.*;

class FormulaLexerException extends IOException
{
	int into;
	int row;
	int col;
	String at;
	
	FormulaLexerException(String msg, int col, int line, int into, String at)
	{
		super(msg);
		this.row = row;
		this.col = col;
		this.into = into;
		this.at = at;
	}
}

%%

%cup
%line
%column
%unicode
%class TermcountLexer

%{

Symbol newSym(int tokenId) 
{
    return new Symbol(tokenId, yyline, yycolumn);
}

Symbol newSym(int tokenId, Object value) 
{
    return new Symbol(tokenId, yyline, yycolumn, value);
}


 

%}

whitespace            = [ \n\r\t]
varname               = [a-z][a-z0-9]*
sortorpredname	      = [A-Z][A-Z0-9]*
arrow		      = "->"

%%

and               { return newSym(sym.AND); }
or                { return newSym(sym.OR); }
not               { return newSym(sym.NOT); }
"|"               { return newSym(sym.BAR); }
":"               { return newSym(sym.COLON); }
"="               { return newSym(sym.EQUALS); }
{arrow}		      { return newSym(sym.ARROW); }
in		          { return newSym(sym.IN); }

forsome           { return newSym(sym.FORSOME); }
forall            { return newSym(sym.FORALL); }

{varname}	      { return newSym(sym.VAR, MFormulaManager.makeVariable(yytext())); }

{sortorpredname}  { return newSym(sym.SORTORPRED, yytext()); }

"("               { return newSym(sym.LPAREN); }
")"		          { return newSym(sym.RPAREN); }

{whitespace}      { /* Ignore whitespace */ }

.		          { throw new FormulaLexerException("Could not start a new lexical token.", yycolumn, yyline, yychar, yytext()); }