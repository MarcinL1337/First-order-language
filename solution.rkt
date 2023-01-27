#lang plait

; Autor: Marcin Linkiewicz, 323853

(module+ test
  (print-only-errors #t))

(define-type Op
  (add) (sub) (mul) (leq))

(define-type Exp
  (numE    [n : Number])
  (varE    [x : Symbol])
  (letE    [x : Symbol] [e1 : Exp] [e2 : Exp])
  (opE     [e1 : Exp] [x : Op] [e2 : Exp])
  (ifzE    [c : Exp] [t : Exp] [f : Exp])
  (defineE [es : (Listof Exp)] [e : Exp])
  (funE    [name : Symbol] [args : (Listof Symbol)] [e : Exp])
  (callE   [name : Symbol] [args : (Listof Exp)]))

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s)
     (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s)
     (varE (s-exp->symbol s))]
    [(s-exp-match? `{let SYMBOL be ANY in ANY} s)
     (letE (s-exp->symbol (second (s-exp->list s)))
           (parse (fourth (s-exp->list s)))
           (parse (first (reverse (s-exp->list s)))))]
    [(s-exp-match? `{ANY SYMBOL ANY} s)
     (opE (parse (first (s-exp->list s)))
          (parse-op (s-exp->symbol (second (s-exp->list s))))
          (parse (third (s-exp->list s))))]
    [(s-exp-match? `{ifz ANY then ANY else ANY} s)
     (ifzE (parse (second  (s-exp->list s)))
           (parse (fourth (s-exp->list s)))
           (parse
            (first (reverse (s-exp->list s)))))]
    [(s-exp-match? `{define {ANY ...} for ANY} s)
     (defineE (parse-list-funs (s-exp->list (second (s-exp->list s))))
              (parse (fourth (s-exp->list s))))]
    [(s-exp-match? `{fun SYMBOL {SYMBOL ...} = ANY} s)
     (funE (s-exp->symbol (second (s-exp->list s)))
           (parse-list-symbols (s-exp->list (third (s-exp->list s))))
           (parse (first (reverse (s-exp->list s)))))]
    [(s-exp-match? `{SYMBOL {ANY ...}} s)
     (callE (s-exp->symbol (first (s-exp->list s)))
            (parse-list-funs (s-exp->list (second (s-exp->list s)))))]
    [else (error 'parse "wrong expression")]))

(define (parse-op op)
  (cond
    [(eq? op '+)  (add)]
    [(eq? op '-)  (sub)]
    [(eq? op '*)  (mul)]
    [(eq? op '<=) (leq)]
    [else (error 'parse-op "unknown operator")]))

(define (parse-list-funs es)
  (type-case (Listof S-Exp) es
    [(cons x xs) (cons (parse x) (parse-list-funs xs))]
    [empty empty]))

(define (parse-list-symbols es)
  (type-case (Listof S-Exp) es
    [(cons e es) (cons (s-exp->symbol e) (parse-list-symbols es))]
    [empty empty]))

; Eval

(define-type-alias Value Number)

(define-type Binding
  (bind    [name : Symbol]
           [val : Value])
  (bind-f  [name : Symbol]
           [function : Exp]))

;; environments

(define-type-alias Env (Listof Binding))

(define mt-env empty)

(define (extend-env [env : Env] [x : Symbol] [v : Value]) : Env
  (cons (bind x v) env))

(define (lookup-env [n : Symbol] [env : Env]) : Value
  (type-case (Listof Binding) env
    [empty (error 'lookup "unbound variable")]
    [(cons b rst-env)
     (if (eq? (bind-name b) n)
         (bind-val b)
         (lookup-env n rst-env))]))

(define (lookup-funs name funs)
  (type-case (Listof Exp) funs
    [(cons x xs)
     (if (eq? name (funE-name x))
         x
         (lookup-funs name xs))]
    [empty (error 'lookup-funs "function not found")]))

(define (call-op op)
  (type-case Op op
    [(add)  +]
    [(sub)  -]
    [(mul)  *]
    [(leq) (lambda (x y) (if (<= x y) 0 1337))]))

(define (eval [e : Exp] [env : Env] [funs : (Listof Exp)]) : Value
  (type-case Exp e
    [(numE n) n]
    [(varE x)
     (lookup-env x env)]
    [(letE x e1 e2)
     (let ([v1 (eval e1 env funs)])
       (eval e2 (extend-env env x v1) funs))]
    [(opE e1 op e2)
     ((call-op op) (eval e1 env funs) (eval e2 env funs))]
    [(ifzE c t f)
     (if (= 0 (eval c env funs))
         (eval t env funs)
         (eval f env funs))]
    [(defineE es e)
     (let [(new-funs (update-funs es funs))]
       (eval e env new-funs))]
    [(callE name args)
     (let [(pom (lookup-funs name funs))]
       (eval (funE-e pom)
             (if (= (length args) (length (funE-args pom)))
                 (eval-args args (funE-args pom) env funs mt-env)
                 (error 'eval
                        "Number of arguments in function doesn't match"))
             funs))]
    [else (error 'eval "wrong expression")]))

; Ewaluuje argumenty podane do funkcji pod warunkiem,
; że ilość podanych i oczekiwanych argumentów się zgadza
(define (eval-args args fun-args env funs acc)
  (type-case (Listof Exp) args
    [(cons x xs)
     (eval-args xs
                (rest fun-args)
                env
                funs
                (extend-env acc (first fun-args) (eval x env funs)))]
    [empty acc]))

; Dodaje funkcje podane w define do listy funkcji w eval
(define (update-funs es funs)
  (type-case (Listof Exp) es
    [(cons x xs) (update-funs xs (cons x funs))]
    [empty funs]))

(define (run [s : S-Exp]) : Value
  (eval (parse s) mt-env '()))

; testy

(test (run `{define
              {}
              for
              (let x be 1337 in (x + 1))})
      1338)

(test (run `{define
              {}
              for
              (let x be 1337 in (ifz (x <= 1338) then x else 0))})
      1337)

(test (run `{define
              {[fun inc-until (x) =
                    {ifz (1337 <= x) then 42 else (inc-until ({x + 1}))}]}
               for
               {inc-until (0)}})
      42)

(test (run `{define
              {[fun dec-until (x) =
                    {ifz (x <= 0) then 42 else (dec-until ({x - 1}))}]}
              for
              {dec-until ({let y be 100 in y})}})
      42)

(test (run `{define
              {[fun fact (n) =
                    {ifz n then 1 else {n * {fact ({n - 1})}}}]}
              for
              {fact (5)}})
      120)

(test (run `{define
              {[fun even (n) = {ifz n then 0 else {odd ({n - 1})}}]
               [fun odd (n) = {ifz n then 42 else {even ({n - 1})}}]}
              for
              {even (1024)}})
      0)

(test (run `{define
              {[fun gcd (m n) = {ifz n
                                     then m
                                     else {ifz {m <= n}
                                               then {gcd (m {n - m})}
                                               else {gcd ({m - n} n)}}}]}
              for
              {gcd (81 63)}})
      9)