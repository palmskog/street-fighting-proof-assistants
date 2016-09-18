{

open ZUtil
open ImpParser

}

let id =
  ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*

let intlit =
  "0" | '-'?['1'-'9']['0'-'9']*

let comment =
  "#"[^'\n']*

let whitespace =
  [' ' '\t']

let line =
  '\n'

rule token = parse
  (* literals *)
  | intlit as x { INTLIT (Big.of_string x) }
  | "True"  { TRUE  }
  | "False" { FALSE }

  (* operators *)
  | "len" { LEN  }
  | "not" { NOT  }
  | "+"   { ADD  }
  | "-"   { SUB  }
  | "*"   { MUL  }
  | "/"   { DIV  }
  | "%"   { MOD  }
  | "=="  { EQ   }
  | "<"   { LT   }
  | "<="  { LE   }
  | "and" { CONJ }
  | "or"  { DISJ }

  (* statements *)
  | "nop"    { NOP    }
  | "="      { ASSIGN }
  | "alloc"  { ALLOC  }
  | ";"      { SEMI   }
  | "if"     { IF     }
  | "else"   { ELSE   }
  | "while"  { WHILE  }
  | "def"    { DEF    }
  | "return" { RET    }

  (* misc *)
  | "," { COMMA   }
  | "(" { LPAREN  }
  | ")" { RPAREN  }
  | "{" { LCURL   }
  | "}" { RCURL   }
  | "[" { LSQUARE }
  | "]" { RSQUARE }
  | eof { EOF     }

  (* variables *)
  | id as x { ID x }

  (* ignore *)
  | comment    { token lexbuf }
  | whitespace { token lexbuf }
  | line       { incr line; token lexbuf }

  (* error *)
  | _ as c
      { failwith (mkstr "ImpLexer: char %c on line %d" c !line) }
