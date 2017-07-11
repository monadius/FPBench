#lang racket

(require "common.rkt" "fpcore.rkt")

(define ((eval-stmts* eval-expr rec) stmts ctx)
  (match-define (cons stmt rest) stmts)
  (match stmt
    [`(output ,exprs ...)
     (map (curryr eval-expr ctx) exprs)]
    [`[= ,var ,expr]
     (rec rest (dict-set ctx var (eval-expr expr ctx)))]
    [`(if)
     (rec rest ctx)]
    [`(if [else ,body ...])
     (rec (append body rest) ctx)]
    [`(if [,test ,body ...] ,tests ...)
     (if (eval-expr test ctx)
         (rec (append body rest) ctx)
         (rec (cons `(if ,@tests) rest) ctx))]
    [`(while ,test ,body ...)
     (if (eval-expr test ctx)
         (rec (append body stmts) ctx)
         (rec rest ctx))]))

(define ((eval-stmts eval-expr) stmts ctx)
  (let loop ([stmts stmts] [ctx ctx])
    ((eval-stmts* eval-expr loop) stmts ctx)))

(module+ main
  (command-line
   #:program "fpimp.rkt"
   #:args args
   (let ([vals (map (compose real->double-flonum string->number) args)])
     (for ([prog (in-port read)])
       (match-define `(FPImp (,vars ...) ,props&body ...) prog)
       (define-values (body props) (parse-properties props&body))
       (define evaltor
         (match (dict-ref props ':type 'binary64)
           ['binary64 racket-double-evaluator]
           ['binary32 racket-single-evaluator]))
       (printf "~a\n" ((eval-stmts (eval-expr racket-double-evaluator)) body (map cons vars vals)))))))
