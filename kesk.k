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

  syntax Exp ::=  "(" "set!" Id Exp ")" [strict(2)]
              |   "(" "define" Id Exp ")"
endmodule

module KESK
  imports KESK-SYNTAX

  syntax Val ::= clo(Id,Exp,Map) [latex(\textsf{closure}((\lambda\: ({#1})\: {#2}), {#3}))]
              |  cc(K,Map)

  syntax Exp ::= mclo(Exp,Map)

  syntax KItem   ::= EnvItem
  syntax EnvItem ::= env(Map)
  syntax KResult ::= Val

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <env color="red"> .Map </env>
//                  <store color="blue"> .Map </store>
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

/*
  rule <k> (clo(X,E,Rho) V:Val) => E ~> env(Rho') ...</k>
       <env> Rho' => Rho[X/X] </env>
       <store>...
         . => <pair>(X |-> V)</pair>
       ...</store>
       //[bucket]
    when fresh(N:Nat) [bucket]
*/

  rule <k> (clo(X,E,Rho) V:Val) => E ~> env(Rho') ...</k>
       <env> Rho' => Rho[N/X] </env>
       <store>...
         . => <pair>(N |-> V)</pair>
       ...</store>
       //[bucket]
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

/*
  rule <k> (mu (X) E) => mclo(E,Rho[X/X]) ...</k>
       <env>Rho</env>
       <store>...
         . => <pair>(X |-> mclo(E,Rho[X/X]))</pair>
       ...</store>
    when fresh(N:Nat) [mubucket,structural]
*/
  rule <k> (mu (X) E) => mclo(E,Rho[N/X]) ...</k>
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

  rule (begin E1)    => E1               [structural]
  rule (begin E1 E2) => E1 ~> (begin E2) [structural]

  rule <k> (set! X:Id V:Val) => . ...</k>
       <env>... X |-> N ...</env>
       <store>...
         <pair> N |-> (_ => V) </pair>
       ...</store>

endmodule

