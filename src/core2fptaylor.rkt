#lang racket

(require "common.rkt" "compilers.rkt" "supported.rkt")
(require "fpcore-reader.rkt" "fpcore-extra.rkt" "range-analysis.rkt")
(provide core->fptaylor fptaylor-supported *fptaylor-inexact-scale*)

(define *fptaylor-inexact-scale* (make-parameter 1))

(define fptaylor-supported 
  (supported-list
    (invert-op-proc 
      (curry set-member?
             '(atan2 cbrt ceil copysign erf erfc exp2 expm1 fdim floor fmod hypot if 
              lgamma log10 log1p log2 nearbyint pow remainder round tgamma trunc while while*)))
    fpcore-consts
    (curry set-member? '(binary16 binary32 binary64 binary128 real))
    ; Note: nearestEven and nearestAway behave identically in FPTaylor
    ieee754-rounding-modes))

; Language-specific reserved names (avoid name collisions)
(define fptaylor-reserved 
  '(Variables variables Definitions definitions Expressions expressions Constraints constraints
    IN in int real float16 float32 float64 float128
    rnd no_rnd rnd16_ne rnd16 rnd16_0 rnd16_down rnd16_up
    rnd32_ne rnd32 rnd32_0 rnd32_down rnd32_up
    rnd64_ne rnd64 rnd64_0 rnd64_down rnd64_up
    rnd128_ne rnd128 rnd128_0 rnd128_down rnd128_up
    inv abs fma sqrt min max exp log cos sin tan cosh sinh tanh
    acos asin atan atan2 arccos arcsin arctan acosh asinh atanh
    arsinh arcosh artanh arcsinh arccosh arctanh argsinh argcosh argtanh
    sub2 floor_power2 interval))

(define (fix-name name)
  (string-join
    (for/list ([char (~a name)])
      (if (regexp-match #rx"[a-zA-Z0-9_]" (string char))
        (string char)
        "_"))
   ""))

(define (inexact-operator? op)
  (set-member? '(exp log sin cos tan asin acos atan
                sinh cosh tanh asinh acosh atanh) op))

(define constant->fptaylor
  (match-lambda
    ['E "exp(1)"]
    ['LN2 "log(2)"]
    ['LN10 "log(10)"]
    ['PI "4 * atan(1)"]
    ['PI_2 "2 * atan(1)"]
    ['PI_4 "atan(1)"]
    ['M_1_PI "1 / (4 * atan(1))"]
    ['M_2_PI "1 / (2 * atan(1))"]
    ['M_2_SQRTPI "1 / sqrt(atan(1))"]
    ['SQRT2 "sqrt(2)"]
    ['SQRT1_2 "1 / sqrt(2)"]
    [c (error 'constant->fptaylor "Unsupported constant ~a" c)]))

(define/match (operator->fptaylor op)
  [('==) '=]
  [((or '+ '- '* '/ 'sqrt '< '> '<= '>=)) op]
  [((or 'exp 'log 'sin 'cos 'tan 'asin 'acos 'atan)) op]
  [((or 'sinh 'cosh 'tanh 'asinh 'acosh 'atanh)) op]
  [('fmax) 'max] [('fmin) 'min] [('fabs) 'abs] [('fma) 'fma]
  [(_) (error 'operator->fptaylor "Unsupported operation ~a" op)])

(define (application->fptaylor operator args)
  (match (cons operator args)
    [(list '- a)
     (format "-~a" a)]
    [(list (or '!= 'not 'and 'or) args ...)
     (error 'application->fptaylor "Unsupported operation ~a" operator)]
    [(list (or '+ '- '* '/ '== '< '> '<= '>=) a b)
     (format "(~a ~a ~a)" a (operator->fptaylor operator) b)]
    [(list (? operator? f) args ...)
     (format "~a(~a)" (operator->fptaylor f) (string-join args ", "))]))

(define/match (prec->fptaylor prec)
  [(#f) ""]
  [('real) "real"]
  [('binary16) "float16"]
  [('binary32) "float32"]
  [('binary64) "float64"]
  [('binary128) "float128"]
  [(_) (error 'prec->fptaylor "Unsupported precision ~a" prec)])

(define/match (rm->fptaylor rm)
  [('nearestEven) "ne"]
  ; The same as 'nearestEven
  [('nearestAway) "ne"]
  [('toPositive) "up"]
  [('toNegative) "down"]
  [('toZero) "zero"]
  [(_) (error 'rm->fptaylor "Unsupported rounding mode ~a" rm)])

(define (round->fptaylor props #:scale [scale 1])
  (define prec (dict-ref props ':precision 'real))
  (define rm (rm->fptaylor (dict-ref props ':round 'nearestEven)))
  (define bits
    (match prec
      [#f "undefined"]
      ['real ""]
      ['binary16 "16"]
      ['binary32 "32"]
      ['binary64 "64"]
      ['binary128 "128"]
      [_ (error 'round->fptaylor "Unsupported precision ~a" prec)]))
  (cond
    [(equal? bits "undefined") "rnd"]
    [(equal? bits "") ""]
    [(and (equal? rm "ne") (= scale 1)) (format "rnd~a" bits)]
    [else (format "rnd[~a,~a,~a]" bits rm scale)]))

(define (number->fptaylor expr props)
  (define n-str (format-number expr))
  (if (string-contains? n-str "/")
      (format "~a~a" (round->fptaylor props) n-str)
      n-str))

(define *defs* (make-parameter '()))

(define (add-def def)
  (*defs* (cons def (*defs*))))

(define (expr->fptaylor expr #:ctx ctx
                        #:inexact-scale [inexact-scale 1])
  ;; Takes in an expression. Returns a string corresponding to this expression and local definitions (in *defs*).
  (match expr
    [`(let ([,vars ,vals] ...) ,body)
      (define ctx*
        (for/fold ([ctx* ctx]) ([var vars] [val vals])
          (let-values ([(cx name) (ctx-unique-name ctx* var)])
            (add-def (format "~a ~a= ~a" name (round->fptaylor (ctx-props ctx))
                      (expr->fptaylor val #:ctx ctx #:inexact-scale inexact-scale)))
            cx)))
     (expr->fptaylor body #:ctx ctx* #:inexact-scale inexact-scale)]

    [`(let* ([,vars ,vals] ...) ,body)
      (define ctx*
        (for/fold ([ctx* ctx]) ([var vars] [val vals])
          (let-values ([(cx name) (ctx-unique-name ctx* var)])
            (add-def (format "~a ~a= ~a" name (round->fptaylor (ctx-props ctx*))
                      (expr->fptaylor val #:ctx ctx* #:inexact-scale inexact-scale)))
            cx)))
     (expr->fptaylor body #:ctx ctx* #:inexact-scale inexact-scale)]

    [`(! ,props ... ,body)
      (define cur-rounding (round->fptaylor (ctx-props ctx)))
      (define new-rounding (round->fptaylor (apply hash-set* #hash() props)))
      (define body* (expr->fptaylor body #:ctx (ctx-update-props ctx props) #:inexact-scale inexact-scale))
      (if (equal? cur-rounding new-rounding)
          body*
          (let-values ([(ctx* tmp-name) (ctx-random-name ctx)])
            (add-def (format "~a ~a= ~a" tmp-name new-rounding body*))
            (format "no_rnd(~a)" tmp-name)))]

    [`(cast ,body)
      (define rounding (round->fptaylor (ctx-props ctx)))
      (define body* (expr->fptaylor body #:ctx ctx #:inexact-scale inexact-scale))
      (let-values ([(ctx* tmp-name) (ctx-random-name ctx)])
        (add-def (format "~a ~a= ~a" tmp-name rounding body*))
        tmp-name)]

    [(list (? operator? operator) args ...)
     (define args-c
       (map (λ (arg) (expr->fptaylor arg #:ctx ctx #:inexact-scale inexact-scale)) args))
     (if (and (inexact-operator? operator) (not (= inexact-scale 1)))
         (let-values ([(ctx* args-c*)
                       (for/fold ([ctx* ctx] [args-c* '()] #:result (values ctx* (reverse args-c*)))
                                 ([arg args-c])
                        (let-values ([(cx tmp-name) (ctx-random-name ctx*)])
                            (add-def (format "~a ~a= ~a" tmp-name (round->fptaylor (ctx-props cx)) arg))
                            (values cx (cons tmp-name args-c*))))])
          (format "~a(~a(~a))" (round->fptaylor (ctx-props ctx*) #:scale inexact-scale)
            (operator->fptaylor operator) (string-join args-c* ", ")))
         (application->fptaylor operator args-c))]

    [(list digits m e b) (number->fptaylor (digits->number m e b) (ctx-props ctx))]
    [(? constant?)
     (format "~a(~a)" (round->fptaylor (ctx-props ctx)) (constant->fptaylor expr))]
    [(? hex?) (number->fptaylor (hex->racket expr) (ctx-props ctx))]
    [(? number?) (number->fptaylor expr (ctx-props ctx))]

    [(? symbol?)
      (let* ([cur-prec (ctx-lookup-prop ctx ':precision 'real)]
             [prec (ctx-lookup-prec ctx expr)]
             [name (ctx-lookup-name ctx expr)])
        (if (equal? cur-prec prec)
            name
            (format "no_rnd(~a)" (ctx-lookup-name ctx expr))))]
))

; This function should be called after remove-let and canonicalize
; (negations should be removed)
(define (conjuncts expr)
  (match expr
    [`(and ,args ...) (append-map conjuncts args)]
    [`(or ,args ...)
     (error 'conjuncts "Logical disjunction is not supported")]
    [`(not ,arg)
     (error 'conjuncts "Logical negation is not supported")]
    [`(,op ,args ...) (list expr)]
    ['TRUE (list expr)]))

; Removes inequalities in the form (cmp var number) and (cmp number var)
(define (select-constraints expr)
  (define conjs (conjuncts expr))
  (filter (match-lambda
            ['TRUE #f]
            ['FALSE (error 'select-constraints "FALSE precondition")]
            [(list (or '!= '== '< '> '<= '>=) (? symbol?) (? number?)) #f]
            [(list (or '!= '== '< '> '<= '>=) (? number?) (? symbol?)) #f]
            [_ #t]) conjs))

(define (core->fptaylor prog name
                         #:precision [precision #f]
                         #:var-precision [var-precision #f]
                         #:indent [indent "  "])
  (parameterize ([*gensym-fix-name* fix-name]
                 [*used-names* (mutable-set)]
                 [*gensym-collisions* 1]
                 [*defs* '()])
    (define-values (core-name args props body)
      (match prog
        [(list 'FPCore (list args ...) props ... body) (values name args props body)]
        [(list 'FPCore name (list args ...) props ... body) (values name args props body)]))
    (define default-ctx (ctx-update-props (make-compiler-ctx) (append `(:precision ,#f :round nearestEven) props)))
    (define ctx (ctx-reserve-names default-ctx fptaylor-reserved))
    (when precision
      (set! ctx (ctx-update-props ctx `(:precision ,precision))))
    (define expr-name 
      (let-values ([(cx name) (ctx-unique-name ctx core-name)])
        (set! ctx cx)
        name))
    ; Arguments
    (define-values (ctx* vars var-names)
      (for/fold ([ctx* ctx] [vars '()] [names '()] 
                 #:result (values ctx* (reverse vars) (reverse names)))
                ([var args])
        (match var
          [`(! ,props ... ,var)
            (define var-props (apply hash-set* (ctx-props ctx) props))
            (define prec (or var-precision (dict-ref var-props ':precision #f)))
            (let-values ([(cx name) (ctx-unique-name ctx* var #:precision prec)])
              (values cx (cons var vars) (cons name names)))]
          [var (let-values ([(cx name) (ctx-unique-name ctx* var #:precision var-precision)])
                (values cx (cons var vars) (cons name names)))])))
    ; Preconditions
    (define pre ((compose canonicalize remove-let)
                 (dict-ref (ctx-props ctx) ':pre 'TRUE)))
    ; Main expression
    (define expr-body (expr->fptaylor body #:ctx ctx* #:inexact-scale (*fptaylor-inexact-scale*)))
    ; Ranges of variables
    (define var-ranges (condition->range-table pre))
    (define arg-strings
      (for/list ([var vars] [var-name var-names])
        (define range
          (cond
            [(and var-ranges (hash-has-key? var-ranges var)) (dict-ref var-ranges var)]
            [else (make-interval -inf.0 +inf.0)]))
        (unless (nonempty-bounded? range)
          (error 'core->fptaylor "Bad range for ~a in ~a (~a)" var expr-name range))
        (unless (= (length range) 1)
          (print range)
          (error 'core->fptaylor "FPTaylor only accepts one sampling range"))
        (match-define (interval l u l? u?) (car range))
        (define prec (ctx-lookup-prec ctx* var))
        (format "~a~a ~a in [~a, ~a];" indent (prec->fptaylor prec) var-name
                (format-number l) (format-number u))))
    ; Other constraints
    ; TODO: inexact-scale is not given to prevent generation of intermediate definitions
    (define constraints
      (map (curry expr->fptaylor #:ctx (ctx-update-props ctx* '(:precision real))) (select-constraints pre)))
    (with-output-to-string
      (λ ()
        (printf "{\n")
        (unless (empty? arg-strings)
          (printf "Variables\n~a\n\n" (string-join arg-strings "\n")))
        (unless (empty? constraints)
          (printf "Constraints\n")
          (for ([c constraints] [n (in-naturals)])
            (define-values (_ c-name) (ctx-unique-name ctx* (format "constraint~a" n)))
            (printf "~a~a: ~a;\n" indent c-name c))
          (printf "\n"))
        (unless (empty? (*defs*))
          (printf "Definitions\n")
          (for ([def (reverse (*defs*))])
            (printf "~a~a;\n" indent def))
          (printf "\n"))
        (printf "Expressions\n~a~a ~a= ~a;\n"
                indent expr-name (round->fptaylor (ctx-props ctx*)) expr-body)
        (printf "}\n")))))

(define-compiler '("fptaylor" "fpt") (const "") core->fptaylor (const "") fptaylor-supported)

(module+ test
  (for ([prog (in-port (curry read-fpcore "test")
                       (open-input-file "../benchmarks/fptaylor-tests.fpcore"))])
    (define progs (fpcore-transform prog #:split-or #t))
    (map (curryr core->fptaylor "test") progs)))

(module+ main
  (require racket/cmdline)
  (define files (make-parameter #f))
  (define files-all (make-parameter #f))
  (define auto-file-names (make-parameter #f))
  (define out-path (make-parameter "."))
  (define precision (make-parameter #f))
  (define var-precision (make-parameter #f))
  (define split-or (make-parameter #f))
  (define subexprs (make-parameter #f))
  (define split (make-parameter #f))
  (define unroll (make-parameter #f))

  (command-line
   #:program "core2fptaylor.rkt"
   #:once-each
   ["--files" "Save FPTaylor tasks corresponding to different FPBench expressions in separate files"
              (files #t)]
   ["--files-all" "Save all FPTaylor tasks in separate files"
                  (files-all #t)]
   ["--auto-file-names" "Generate special names for all files"
                        (auto-file-names #t)]
   ["--out-path" path "All files are saved in the given path"
                 (out-path path)]
   ["--precision" prec "The precision of all operations (overrides the :precision property)"
                  (precision (string->symbol prec))]
   ["--var-precision" prec "The precision of input variables (overrides the :var-precision property)"
                      (var-precision (string->symbol prec))]
   ["--scale" scale "The scale factor for operations which are not correctly rounded"
              (*fptaylor-inexact-scale* (string->number scale))]
   ["--split-or" "Convert preconditions to DNF and create separate FPTaylor tasks for all conjunctions"
                 (split-or #t)]
   ["--subexprs" "Create FPTaylor tasks for all subexpressions"
                 (subexprs #t)]
   ["--split" n "Split intervals of bounded variables into the given number of parts"
              (split (string->number n))]
   ["--unroll" n "How many iterations to unroll any loops to"
               (unroll (string->number n))]
   #:args ([input-file #f])
   ((if input-file
        (curry call-with-input-file input-file)
        (λ (proc) (proc (current-input-port))))
    (λ (port)
      (port-count-lines! port)
      (for ([prog (in-port (curry read-fpcore "input") port)] [n (in-naturals)])
        ;;; (with-handlers ([exn:fail? (λ (exn) (eprintf "[ERROR]: ~a\n\n" exn))])
          (define def-name (format "ex~a" n))
          (define prog-name (if (auto-file-names) def-name (fpcore-name prog def-name)))
          (define progs (fpcore-transform prog
                                          #:unroll (unroll)
                                          #:split (split)
                                          #:subexprs (subexprs)
                                          #:split-or (split-or)))
          (define results (map (curryr core->fptaylor def-name
                                      #:precision (precision)
                                      #:var-precision (var-precision)
                                      #:indent "  ")
                               progs))
          (define multiple-results (> (length results) 1))
          (cond
            [(files-all)
             (for ([r results] [k (in-naturals)])
               (define fname (fix-file-name
                              (string-append prog-name
                                             (if multiple-results (format "_case~a" k) "")
                                             ".txt")))
               (call-with-output-file (build-path (out-path) fname) #:exists 'replace
                 (λ (p) (fprintf p "~a" r))))]
            [(files)
             (define fname (fix-file-name (format "~a.txt" prog-name)))
             (call-with-output-file (build-path (out-path) fname) #:exists 'replace
               (λ (p) (for ([r results])
                        (if multiple-results (fprintf p "~a\n" r) (fprintf p "~a" r)))))]
            [else (for ([r results]) (printf "~a\n" r))])
          )))
  ))