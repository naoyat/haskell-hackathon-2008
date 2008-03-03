(use srfi-1)

(define *undefined* (if #f #f))

(define (tagged? tag obj) (and (pair? obj) (eq? (car obj) tag)))
(define (tagged?$ tag) (lambda (obj) (and (pair? obj) (eq? (car obj) tag))))
(define (tag t obj) (cons t obj))
(define (tag$ t) (lambda (obj) (cons t obj)))
(define (untag obj) (cdr obj))

(use peg)

(define (nil-if-true l) (if (eq? #t l) '() l))
(define ($my-sep-by parse sep . args)
  ($do (them ($sep-by parse sep))
	   ($return (nil-if-true them))))

(define %ws ($many ($one-of #[ \t\r\n])))

(define %string ; scheme-string で代用
  (let* ([%dquote ($char #\")]
         [%unescaped ($none-of #[\"])]
         [%body-char ($or %unescaped)]
         [%string-body ($do (chars ($many %body-char))
							($return (tag :string (list->string chars))))]
		 )
	($between %dquote %string-body %dquote)))

(define %ident ;; scheme-symbolで代用
  (let* ([%ident-head-char ($one-of #[a-z_])]
		 [%ident-rest-char ($one-of #[0-9A-Za-z_'])])
	($do (head %ident-head-char)
		 (rest ($many %ident-rest-char))
		 ($return (string->symbol (list->string (cons head rest)))))))

(define %digits
  ($do (d ($many digit 1))
	   ($return (tag :number (string->number (list->string d))))))

(define %list
  (let* ([%begin-list ($seq %ws ($char #\[) %ws)]
		 [%end-list ($seq %ws ($char #\]) %ws)]
		 [%item ($or %digits %string %ident)]
		 [%item-separator ($seq %ws ($char #\,) %ws)]
		 )
	($do %begin-list
		 (items ($my-sep-by %item %item-separator))
		 %end-list
		 ($return (tag :list items)))
	))

(define %tuple
  (let* ([%begin-list ($seq %ws ($char #\() %ws)]
		 [%end-list ($seq %ws ($char #\)) %ws)]
		 [%item ($or %digits %string %ident)]
		 [%item-separator ($seq %ws ($char #\,) %ws)]
		 )
	($do %begin-list
		 (items ($my-sep-by %item %item-separator))
		 %end-list
		 ($return (tag :tuple @items)))
	))

(define %expr
  ($or %string %digits %ident %list %tuple))

(define %application
  (let1 %an-application
	  ($do (fn %ident)
		   %ws
		   (args ($my-sep-by %expr %ws))
		   ($return `(:apply ,fn ,@args)))
	($do (app1 %an-application)
		 (apps ($many ($do %ws
						   (($char #\$))
						   %ws
						   (app %an-application)
						   ($return app))))
		 ($return (if (= 0 (length apps)) app1 `(:$ ,app1 ,@apps))))))

(define %haskell
  (let* ([%unknown ($my-sep-by %expr %ws)]
		 
		 [%assignment ($do (id %ident)
						   %ws
						   (($string "<-"))
						   %ws
						   (value %application)
						   ($return `(:assign ,id ,value))
						   )]
		 [%do-line-separator ($seq %ws ($or ($seq newline ($string "  ")) ($char #\;)) %ws)]
		 [%do ($do (($string "do"))
				   %ws
				   (exprs ($or ($between ($seq ($char #\{) %ws)
										 ($my-sep-by ($or %assignment %application)
													 ($seq %ws ($char #\;) ($optional ($seq newline ($string "  "))) %ws))
										 ($seq %ws ($char #\})))
							   ($my-sep-by ($or %assignment %application)
										   ($seq newline ($string "  ") %ws)) ))
				   ($return `(:do ,@exprs)))]

		 [%defun ($do (id %ident)
					  %ws
					  (args ($my-sep-by %ident %ws))
					  %ws
					  (($char #\=))
					  %ws
					  (rightside ($or %do %application))
					  ($return `(:defun (,id ,@args) ,rightside))
					  )]
		 [%pattern ($do (id %ident)
						%ws
						(args ($my-sep-by ($or %ident %digits) %ws))
						%ws
						(($char #\=))
						%ws
						(rightside ($or %do %application))
						($return `(:pattern (,id ,@args) ,rightside))
						)]

		 )
	($or %defun %pattern %assignment %application %expr
		 %unknown)
	))

(define (parse-haskell str)
  (parse-string %haskell str))
		  
(define putStrLn print)

(define ident? symbol?)
(define ident-body identity)
;(define ident? (tagged?$ :ident))
;(define ident-body untag)

(define (indent w lines)
  (string-join (map (lambda (line) (string-append (make-string w #\space) (x->string line)))
					lines)
			   "\n"))

(define *namespace* (make-hash-table))
(define (assign id val)
  (hash-table-put! *namespace* id val)
  id)
(define (lookup id)
  (let1 val (hash-table-get *namespace* id)
	;
	val))

;;
(define (make-procedure params body env)
  (list :procedure params body env))

(use util.match)
(define (heval-map exps env) (map (cut heval <> env) exps))
(define (heval exp env)
  (if (or (null? exp) (not (pair? exp))) *undefined*
	  (match exp
		[(':$ . _)
;		 (delay-it
		  (let loop ([rest (cdr exp)])
			(if (null? (cdr rest))
				(heval (car rest) env)
				(heval (append (car rest) (list (loop (cdr rest)))) env)
				))
;		  env)
		  ]
		[(':apply f . _)
		 (if (null? (cddr exp))
;			 (delay-it (list (ident-body f)) env)
			 (list (ident-body f))
			 `(,(ident-body f) ,@(cddr exp)); ,@(map (cut heval <> env) (cdr exp)))
;			 (delay-it `(,(ident-body f)
;						 ,@(map (cut heval <> env) (cdr exp)))
;					   env)
			 )]
		[(':assign x y) ; id <- action
		 (assign (ident-body x) (heval y env))]
		[(':do . _) ; do { ... ; ... ; ... }
		 `(seq ,@(heval-map (cdr exp) env))]
		[(':defun id definition) ; id x y z = app x $ app y $ app z
		 (let ([ident (car id)]
			   [args (cdr id)])
		   (assign (ident-body ident)
				   (make-procedure (map ident-body args) ;lambda-parameters
								   (if (eq? 'seq (car definition)) ; lambda-body
									   (heval definition env)
									   (list (heval definition env)) )
								   env)))]
		[(':pattern id definition) ; id x y z = app x $ app y $ app z
		 (let ([ident (car id)]
			   [args (cdr id)])
		   (assign (ident-body ident)
				   (make-procedure (map ident-body args) ;lambda-parameters
								   (if (eq? 'seq (car definition)) ; lambda-body
									   (heval definition env)
									   (list (heval definition env)) )
								   env)))]
		
		[(':string . str) str]
		[(':list . l) l]
		[(':tuple . t) t]
		[(':ident . id) id]

		[_ (if (pair? exp) (happly (car exp) (cdr exp))
			   (format "unknown: ~a" exp))] )))

(define (primitive-procedure? proc)
  (memq proc '(putStr 
			   putStrLn
			   lines length print
			   tail)))

(define (prim-print exp)
  (define (haskell-description-of-list l)
	(string-append "[" (string-join (map haskell-description l) ",") "]"))
	
  (define (haskell-description obj)
	(cond [(not (pair? obj)) (x->string obj)]
		  [(tagged? :number obj) (number->string (untag obj))]
		  [(tagged? :string obj) (untag obj)]
		  [(tagged? :list obj) ; (untag obj)]
		   (list->haskell-string (untag obj))]
		  [(pair? obj) (haskell-description-of-list obj)]
		  [else (x->string obj)]))

  (print (haskell-description exp)))

(define (prim-tail exp)
  (cond [(tagged? :string exp) (substring (cdr exp) 1 (string-length (cdr exp)))]
		[(tagged? :list exp) (cddr exp)]
		[(pair? exp) (cdr exp)]
		[else *undefined*]))

(define (apply-primitive-procedure proc args)
  (let1 args* (heval-map args '())
	(case proc
	  ((putStr) (display (x->string (car args*))))
	  ((putStrLn) (apply prim-print args*))
	  ((print) (apply prim-print args*))
	  ((lines) (length args*))
	  ((length) (if (tagged? :string (car args*))
					(string-length (car args*))
					(length (car args*))))
	  ((tail) (prim-tail (car args*)))
	  )))

(define (compound-procedure? proc) (tagged? :procedure proc))

(define (procedure-parameters proc) (second proc))
(define (procedure-body proc) (third proc))
(define (procedure-environment proc) (fourth proc))

(define (make-frame vars vals) (cons vars vals))

(define (extend-environment vars vals base-env)
  ;; assert-equal (length vars) (length vals)
  (cons (make-frame vars vals) base-env))

(define (happly proc args)
  (cond [(primitive-procedure? proc)
		 (apply-primitive-procedure proc args)]
		[(compound-procedure? proc)
		 (let1 env (extend-environment (procedure-parameters proc)
									   args
									   (procedure-environment proc))
		   (heval-map (procedure-body proc) env))]
		[else
		 ;
		 ]))

;; REPL
(let repl ()
  (let1 input (read-line)
	(if (eof-object? input) 'eof
		(let1 parsed (parse-haskell input); (haskell->scheme input)
		  (let1 evaled (heval parsed '())
			(print "> " input)
			(print "=> " parsed)
			(print "" evaled))
		  (repl)))))

(define (actual-value exp); env)
  (force-it (heval exp '())))

(let1 main (lookup 'main)
  (print "----")
   (happly main '())
   )
