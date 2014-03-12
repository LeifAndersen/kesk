module KESK-SYNTAX

  syntax Val ::= Int | Bool

  syntax Exp ::= Val
              |  "(" Exp Exp ")" [strict]
              |  Id
              |  "(" "lambda" "(" Id ")" Exp ")" [latex((\lambda\: ({#1})\: {#2}))]

  syntax Exp ::= "(" "*" Exp Exp ")"  [strict]
              |  "(" "/" Exp Exp ")"  [strict]
              |  "(" "+" Exp Exp ")"  [strict]
              |  "(" "=" Exp Exp ")"  [strict]
              |  "(" "<" Exp Exp ")"  [strict]
              |  "(" ">" Exp Exp ")"  [strict]
              |  "(" "<=" Exp Exp ")" [strict]
              |  "(" ">=" Exp Exp ")" [strict]
              |  "(" "not" Exp ")"    [strict]

  syntax Exp ::= "(" "if" Exp Exp Exp ")" [strict(1)]
              |  "(" "let" "(" "[" Id Exp "]" ")" Exp ")"
              | "(" "letrec" "(" "[" Id "(" "lambda" "(" Id ")" Exp ")" "]" ")" Exp ")"
              | "(" "mu" "(" Id ")" Exp ")" [latex((\mu\: ({#1})\: {#2}))]

  syntax Exp ::= "(" "call/cc" Exp ")" [strict]

  syntax Exp ::= "(" "begin" Exp Exp ")"
              | "(" "begin" Exp ")"
              | "(" "begin" Exp Exp Exp ")"
              | "(" "begin" Exp Exp Exp Exp ")"
              | "(" "begin" Exp Exp Exp Exp Exp ")"

  syntax Exp ::=  "(" "set!" Id Exp ")"  [strict(2)]
              |   "(" "define" Id Exp ")"
              |   "(" "quote" Exp ")"
              |   "'" Exp
              |   Pair

  syntax Pair ::= "(" "cons" Exp Exp ")" [strict]
               |   "'" "(" ")"

  syntax Exp ::= "(" "map" Exp Exp ")"  [strict]
endmodule

module KESK
  imports KESK-SYNTAX

  syntax Val ::= Clo
              |  cc(K,Map)
              |  quote(Exp)
              |  pair(Val,Val)
              |  "null"

  syntax Clo ::= clo(Id,Exp,Map) [latex(\textsf{closure}((\lambda\: ({#1})\: {#2}), {#3}))]

  syntax Exp ::= mclo(Exp,Map)

  syntax KItem   ::= EnvItem
  syntax EnvItem ::= env(Map)
  syntax KResult ::= Val

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <env color="red"> .Map </env>
                  <store color="blue">
                    <pair multiplicity="*" color="orange"> .Map </pair>
                  </store>
                </T>

  rule <k> X => V ...</k>
       <env>... X |-> A ...</env>
       <store>...
          <pair>(A |-> V)</pair>
       ...</store> [lookup]

  rule <k> (lambda (X:Id) E) => clo(X,E,Rho) ...</k>
       <env> Rho </env>
    [structural]

  arule <k> (clo(X,E,Rho) V:Val) => E ~> env(Rho') ...</k>
       <env> Rho' => Rho[X/X] </env>
       <store>...
         . => <pair>(X |-> V)</pair>
       ...</store>
       [bucket]

  crule <k> (clo(X,E,Rho) V:Val) => E ~> env(Rho') ...</k>
       <env> Rho' => Rho[N/X] </env>
       <store>...
         . => <pair>(N |-> V)</pair>
       ...</store>
    when fresh(N:Nat) [bucket]

  rule <k> _:Val ~> (env(Rho) => .) ...</k>
       <env> _ => Rho </env>
    [structural]

  rule <k>... env(Rho) => . ...</k>
       <env> Rho </env>
       <store>...
         <pair>(A |-> B)</pair>
         (<pair>(A |-> B)</pair> => .)
       ...</store>

  rule (* I1:Int I2:Int)  => I1 *Int I2
  rule (/ I1:Int I2:Int)  => I1 /Int I2
  rule (+ I1:Int I2:Int)  => I1 +Int I2
  rule (= I1:Int I2:Int)  => I1 ==Int I2
  rule (< I1:Int I2:Int)  => I1 <Int I2
  rule (> I1:Int I2:Int)  => I1 <Int I2
  rule (<= I1:Int I2:Int) => I1 <Int I2
  rule (>= I1:Int I2:Int) => I1 <Int I2
  rule (not I1:Bool)      => notBool I1

  rule (if true E _)    => E
  rule (if false _ E)   => E
  rule (let ([X E]) E') => ((lambda (X) E') E) [macro]
  rule (letrec ([F:Id (lambda (X) E)]) E') => (let ([F (mu (F) (lambda (X) E))]) E') [macro]

  arule <k> (mu (X) E) => mclo(E,Rho[X/X]) ...</k>
       <env>Rho</env>
       <store>...
         . => <pair>(X |-> mclo(E,Rho[X/X]))</pair>
       ...</store>
       [mubucket,structural]

  crule <k> (mu (X) E) => mclo(E,Rho[N/X]) ...</k>
       <env>Rho</env>
       <store>...
         . => <pair>(N |-> mclo(E,Rho[N/X]))</pair>
       ...</store>
    when fresh(N:Nat) [mubucket,structural]

  rule <k>mclo(E,Rho) => E ~> env(Rho') ...</k>
       <env>Rho' => Rho</env>

  rule <k> ((call/cc V:Val) => (V cc(K,Rho))) ~> K </k>
       <env> Rho </env>
  rule <k> (cc(K,Rho) V) ~> _ => V ~> K </k>
       <env> _ => Rho </env>

  rule (begin E1)             => E1                        [structural]
  rule (begin E1 E2)          => E1 ~> (begin E2)          [structural]
  rule (begin E1 E2 E3)       => E1 ~> (begin E2 E3)       [structural]
  rule (begin E1 E2 E3 E4)    => E1 ~> (begin E2 E3 E4)    [structural]
  rule (begin E1 E2 E3 E4 E5) => E1 ~> (begin E2 E3 E4 E5) [structural]

  rule <k> (set! X:Id V:Val) => . ...</k>
       <env>... X |-> N ...</env>
       <store>...
         <pair> N |-> (_ => V) </pair>
       ...</store>

  rule (cons E1:Val E2:Val) => pair(E1, E2)
  rule (quote E1)           => quote(E1)

  rule 'E1                  => quote(E1)

  rule '()                  => null

  rule (map E:Clo pair(A,B))   => (cons (E A) (map E B))
  rule (map clo(X,E,Rho) null) => null

endmodule

